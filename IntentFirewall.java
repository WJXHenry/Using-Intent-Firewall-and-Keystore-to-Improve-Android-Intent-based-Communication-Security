/*
 * Copyright (C) 2013 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.server.firewall;

import android.app.AppGlobals;
import android.content.ComponentName;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.pm.ApplicationInfo;
import android.content.pm.IPackageManager;
import android.content.pm.PackageManager;
import android.content.pm.PackageManager.NameNotFoundException;
import android.os.Environment;
import android.os.FileObserver;
import android.os.Handler;
import android.os.Looper;
import android.os.Message;
import android.os.RemoteException;
import android.util.ArrayMap;
import android.util.Slog;
import android.util.Xml;
import com.android.internal.util.ArrayUtils;
import com.android.internal.util.XmlUtils;
import com.android.server.EventLogTags;
import com.android.server.IntentResolver;
import org.xmlpull.v1.XmlPullParser;
import org.xmlpull.v1.XmlPullParserException;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

// Intent Firewall Edit
import android.content.pm.PackageManager;
import android.content.pm.PackageInfo;
import android.content.pm.Signature;
import android.os.Binder;
import android.os.Process;
import android.os.UserHandle;
import android.security.KeyStore;
import android.util.Log;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayInputStream;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.math.BigInteger;
import java.security.cert.CertificateException;
import java.security.cert.CertificateFactory;
import java.security.cert.X509Certificate;
import java.security.interfaces.DSAPublicKey;
import java.security.interfaces.RSAPublicKey;
import java.util.Arrays;
// Intent Firewall Edit

public class IntentFirewall {
    static final String TAG = "IntentFirewall";

    // e.g. /data/system/ifw or /data/secure/system/ifw
    private static final File RULES_DIR = new File(Environment.getDataSystemDirectory(), "ifw");

    private static final int LOG_PACKAGES_MAX_LENGTH = 150;
    private static final int LOG_PACKAGES_SUFFICIENT_LENGTH = 125;

    private static final String TAG_RULES = "rules";
    private static final String TAG_ACTIVITY = "activity";
    private static final String TAG_SERVICE = "service";
    private static final String TAG_BROADCAST = "broadcast";

    private static final int TYPE_ACTIVITY = 0;
    private static final int TYPE_BROADCAST = 1;
    private static final int TYPE_SERVICE = 2;

    private static final HashMap<String, FilterFactory> factoryMap;

    private final AMSInterface mAms;

    private final RuleObserver mObserver;

    private FirewallIntentResolver mActivityResolver = new FirewallIntentResolver();
    private FirewallIntentResolver mBroadcastResolver = new FirewallIntentResolver();
    private FirewallIntentResolver mServiceResolver = new FirewallIntentResolver();

    static {
        FilterFactory[] factories = new FilterFactory[] {
                AndFilter.FACTORY,
                OrFilter.FACTORY,
                NotFilter.FACTORY,

                StringFilter.ACTION,
                StringFilter.COMPONENT,
                StringFilter.COMPONENT_NAME,
                StringFilter.COMPONENT_PACKAGE,
                StringFilter.DATA,
                StringFilter.HOST,
                StringFilter.MIME_TYPE,
                StringFilter.SCHEME,
                StringFilter.PATH,
                StringFilter.SSP,

                CategoryFilter.FACTORY,
                SenderFilter.FACTORY,
                SenderPackageFilter.FACTORY,
                SenderPermissionFilter.FACTORY,
                PortFilter.FACTORY
        };

        // load factor ~= .75
        factoryMap = new HashMap<String, FilterFactory>(factories.length * 4 / 3);
        for (int i=0; i<factories.length; i++) {
            FilterFactory factory = factories[i];
            factoryMap.put(factory.getTagName(), factory);
        }
    }

    public IntentFirewall(AMSInterface ams, Handler handler) {
        
        // Intent Firewall Edit
        needsUpdating = true;
        // Intent Firewall Edit

        mAms = ams;
        mHandler = new FirewallHandler(handler.getLooper());
        File rulesDir = getRulesDir();
        rulesDir.mkdirs();

        // Intent Firewall Edit
        try {
            Log.d("IntentFirewall", "Attempting to get keystore instance");
            mKeyStore = KeyStore.getInstance();
        } catch (Exception e) {
            Log.d("IntentFirewall", e.getMessage());
        }

        // list the keys stored in the keystore (sorted)
        listAllKeys(true);
        // Intent Firewall Edit

        readRulesDir(rulesDir);

        mObserver = new RuleObserver(rulesDir);
        mObserver.startWatching();
    }

    /**
     * This is called from ActivityManager to check if a start activity intent should be allowed.
     * It is assumed the caller is already holding the global ActivityManagerService lock.
     */
    public boolean checkStartActivity(Intent intent, int callerUid, int callerPid,
            String resolvedType, ApplicationInfo resolvedApp) {
        return checkIntent(mActivityResolver, intent.getComponent(), TYPE_ACTIVITY, intent,
                callerUid, callerPid, resolvedType, resolvedApp.uid);
    }

    public boolean checkService(ComponentName resolvedService, Intent intent, int callerUid,
            int callerPid, String resolvedType, ApplicationInfo resolvedApp) {
        return checkIntent(mServiceResolver, resolvedService, TYPE_SERVICE, intent, callerUid,
                callerPid, resolvedType, resolvedApp.uid);
    }

    public boolean checkBroadcast(Intent intent, int callerUid, int callerPid,
            String resolvedType, int receivingUid) {
        return checkIntent(mBroadcastResolver, intent.getComponent(), TYPE_BROADCAST, intent,
                callerUid, callerPid, resolvedType, receivingUid);
    }

    public boolean checkIntent(FirewallIntentResolver resolver, ComponentName resolvedComponent,
            int intentType, Intent intent, int callerUid, int callerPid, String resolvedType,
            int receivingUid) {

        // Log.d("IntentFirewall", "checkIntent: START");

        boolean log = false;
        boolean block = false;

        // Intent Firewall Edit
        // Note: it is easier to just intercept calls from user-installed apps
        // Therefore we should start checking when callerUid is greater than 10059 (last pre-installed apps UID)
        // (If the calling uid is that of a system app, allow)
        if (callerUid > 10059 && callerUid <= Process.LAST_APPLICATION_UID) {

            // Log the uids
            Log.d("IntentFirewall", "checkIntent: caller was an application: " + String.valueOf(callerUid));
            Log.d("IntentFirewall", "checkIntent: receiving Uid: " + String.valueOf(receivingUid));

            // Allow IPC within the app itself (caller = receiver)
            if (callerUid != receivingUid) {
                if (intent.getAction() != null) {
                    Log.d("IntentFirewall", intent.getAction());
                }

                // Tests if both the caller uid and receiver uid are valid - both must be valid in
                // order for the IPC to be allowed to happen
                try {
                    // Block if the caller uid is not valid (not in keystore or keys do not match)
                    Log.d("IntentFirewall", "Checking caller uid");
                    if (!isValidUid(callerUid)) {
                        Log.d("IntentFirewall", "Block intent");
                        block = true;
                    } else {
                        // Allow if the receiving uid is not a an application uid (system)
                        // If it is an application uid, we still have to check if it is valid
                        if (receivingUid > 10059 && receivingUid <= Process.LAST_APPLICATION_UID) {
                            Log.d("IntentFirewall", "Checking receiver uid");
                            // Block if the receiving uid is not valid as well
                            if (!isValidUid(receivingUid)) {
                                Log.d("IntentFirewall", "Block intent");
                                block = true;
                            }
                        }
                    }
                } catch (Exception e) {
                    Log.d("IntentFirewall", "Check keys ERROR: " + e.getMessage());
                }
            } else {
                Log.d("IntentFirewall", "Calling app = Receiving app - Allow");
            }
        }

        if (intent.getAction() != null) {
            // catch the BOOT_COMPLETED action to update keys once android is finished booting
            if (needsUpdating && intent.getAction().equals("android.intent.action.BOOT_COMPLETED")) {
                insertKeysToKeyStore(listOfPackages);
                needsUpdating = false;
            }
            // catch the install success action from PackageInstaller to insert new key into keystore
            if (intent.getAction().equals("com.android.packageinstaller.ACTION_INSTALL_SUCCESS")) {
                Log.d("IntentFirewall", "Installing app from PackageInstaller");

                Log.d("IntentFirewall", "checkIntent: calling Uid: " + String.valueOf(callerUid));
                Log.d("IntentFirewall", "checkIntent: receiving Uid: " + String.valueOf(receivingUid));

                // get the package name from the intent extra field
                String mPackageName = intent.getStringExtra(Intent.EXTRA_INTENT_FIREWALL);
                // init IPackageManager instance
                IPackageManager mIPackageManager = AppGlobals.getPackageManager();
                
                try {
                    Log.d("IntentFirewall", "Storing key into keystore");
                    // get the public key of the installed app
                    BigInteger key = getPubKeyModulus(mPackageName, mIPackageManager);
                    // get the uid of the installed app
                    int packageUid = mIPackageManager.getPackageUid(mPackageName, PackageManager.MATCH_ANY_USER, 
                        UserHandle.USER_SYSTEM);
                    // put the key in the keystore
                    mKeyStore.put(String.valueOf(packageUid), key.toByteArray(), UserHandle.USER_SYSTEM, KeyStore.FLAG_NONE);
                    Log.d("IntentFirewall", "Stored key: " + String.valueOf(packageUid) + ": " + String.valueOf(key));
                    // Log.d("IntentFirewall", "attempt to retreive key from keystore");
                    // byte[] data = mKeyStore.get("KeyTesting", UserHandle.USER_SYSTEM);
                    // BigInteger retreivedKey = new BigInteger(data);
                    // Log.d("IntentFirewall", "value of retreived key: " + String.valueOf(retreivedKey));
                } catch (Exception e) {
                    Log.d("IntentFirewall", "Storing key into keystore error: " + e.getMessage());
                }
            }
            // catch the uninstall action from PackageInstaller to delete key from keystore
            if (intent.getAction().equals("com.android.packageinstaller.ACTION_UNINSTALL_COMMIT")) {
                Log.d("IntentFirewall", "Uninstalling app from PackageInstaller");
                // return -1 if no value stored
                int pUid = intent.getIntExtra(Intent.EXTRA_INTENT_FIREWALL, -1);
                Log.d("IntentFirewall", "Key being deleted: " + String.valueOf(pUid));
                if (mKeyStore.contains(String.valueOf(pUid), UserHandle.USER_SYSTEM)) {
                    boolean deleted = mKeyStore.delete(String.valueOf(pUid), UserHandle.USER_SYSTEM);
                    Log.d("IntentFirewall", "Deleted key: " + String.valueOf(deleted));
                } else {
                    Log.d("IntentFirewall", "Key not in keystore");
                }
            }
            // catch the uninstall action (not from PackageInstaller) to delete key from keystore
            if (intent.getAction().equals("com.android.packageinstaller.UNINSTALL_REMOVE_KEY")) {
                Log.d("IntentFirewall", "Uninstalling app");
                // return -1 if no value stored
                int pUid = intent.getIntExtra(Intent.EXTRA_INTENT_FIREWALL, -1);
                Log.d("IntentFirewall", "Key being deleted: " + String.valueOf(pUid));
                if (mKeyStore.contains(String.valueOf(pUid), UserHandle.USER_SYSTEM)) {
                    boolean deleted = mKeyStore.delete(String.valueOf(pUid), UserHandle.USER_SYSTEM);
                    Log.d("IntentFirewall", "Deleted key: " + String.valueOf(deleted));
                } else {
                    Log.d("IntentFirewall", "Key not in keystore");
                }
            }
        }
        // Intent Firewall Edit

        // For the first pass, find all the rules that have at least one intent-filter or
        // component-filter that matches this intent
        List<Rule> candidateRules;
        candidateRules = resolver.queryIntent(intent, resolvedType, false /*defaultOnly*/, 0);
        if (candidateRules == null) {
            candidateRules = new ArrayList<Rule>();
        }
        resolver.queryByComponent(resolvedComponent, candidateRules);

        // For the second pass, try to match the potentially more specific conditions in each
        // rule against the intent
        for (int i=0; i<candidateRules.size(); i++) {
            Rule rule = candidateRules.get(i);
            if (rule.matches(this, resolvedComponent, intent, callerUid, callerPid, resolvedType,
                    receivingUid)) {
                block |= rule.getBlock();
                log |= rule.getLog();

                // if we've already determined that we should both block and log, there's no need
                // to continue trying rules
                if (block && log) {
                    break;
                }
            }
        }

        if (log) {
            logIntent(intentType, intent, callerUid, resolvedType);
        }

        // Log.d("IntentFirewall", "checkIntent: END");

        return !block;
    }

    private static void logIntent(int intentType, Intent intent, int callerUid,
            String resolvedType) {
        // The component shouldn't be null, but let's double check just to be safe
        ComponentName cn = intent.getComponent();
        String shortComponent = null;
        if (cn != null) {
            shortComponent = cn.flattenToShortString();
        }

        String callerPackages = null;
        int callerPackageCount = 0;
        IPackageManager pm = AppGlobals.getPackageManager();
        if (pm != null) {
            try {
                String[] callerPackagesArray = pm.getPackagesForUid(callerUid);
                if (callerPackagesArray != null) {
                    callerPackageCount = callerPackagesArray.length;
                    callerPackages = joinPackages(callerPackagesArray);
                }
            } catch (RemoteException ex) {
                Slog.e(TAG, "Remote exception while retrieving packages", ex);
            }
        }

        EventLogTags.writeIfwIntentMatched(intentType, shortComponent, callerUid,
                callerPackageCount, callerPackages, intent.getAction(), resolvedType,
                intent.getDataString(), intent.getFlags());
    }

    /**
     * Joins a list of package names such that the resulting string is no more than
     * LOG_PACKAGES_MAX_LENGTH.
     *
     * Only full package names will be added to the result, unless every package is longer than the
     * limit, in which case one of the packages will be truncated and added. In this case, an
     * additional '-' character will be added to the end of the string, to denote the truncation.
     *
     * If it encounters a package that won't fit in the remaining space, it will continue on to the
     * next package, unless the total length of the built string so far is greater than
     * LOG_PACKAGES_SUFFICIENT_LENGTH, in which case it will stop and return what it has.
     */
    private static String joinPackages(String[] packages) {
        boolean first = true;
        StringBuilder sb = new StringBuilder();
        for (int i=0; i<packages.length; i++) {
            String pkg = packages[i];

            // + 1 length for the comma. This logic technically isn't correct for the first entry,
            // but it's not critical.
            if (sb.length() + pkg.length() + 1 < LOG_PACKAGES_MAX_LENGTH) {
                if (!first) {
                    sb.append(',');
                } else {
                    first = false;
                }
                sb.append(pkg);
            } else if (sb.length() >= LOG_PACKAGES_SUFFICIENT_LENGTH) {
                return sb.toString();
            }
        }
        if (sb.length() == 0 && packages.length > 0) {
            String pkg = packages[0];
            // truncating from the end - the last part of the package name is more likely to be
            // interesting/unique
            return pkg.substring(pkg.length() - LOG_PACKAGES_MAX_LENGTH + 1) + '-';
        }
        return null;
    }

    public static File getRulesDir() {
        return RULES_DIR;
    }

    /**
     * Reads rules from all xml files (*.xml) in the given directory, and replaces our set of rules
     * with the newly read rules.
     *
     * We only check for files ending in ".xml", to allow for temporary files that are atomically
     * renamed to .xml
     *
     * All calls to this method from the file observer come through a handler and are inherently
     * serialized
     */
    private void readRulesDir(File rulesDir) {
        FirewallIntentResolver[] resolvers = new FirewallIntentResolver[3];
        for (int i=0; i<resolvers.length; i++) {
            resolvers[i] = new FirewallIntentResolver();
        }

        File[] files = rulesDir.listFiles();
        if (files != null) {
            for (int i=0; i<files.length; i++) {
                File file = files[i];

                if (file.getName().endsWith(".xml")) {
                    readRules(file, resolvers);
                }
            }
        }

        Slog.i(TAG, "Read new rules (A:" + resolvers[TYPE_ACTIVITY].filterSet().size() +
                " B:" + resolvers[TYPE_BROADCAST].filterSet().size() +
                " S:" + resolvers[TYPE_SERVICE].filterSet().size() + ")");

        synchronized (mAms.getAMSLock()) {
            mActivityResolver = resolvers[TYPE_ACTIVITY];
            mBroadcastResolver = resolvers[TYPE_BROADCAST];
            mServiceResolver = resolvers[TYPE_SERVICE];
        }
    }

    /**
     * Reads rules from the given file and add them to the given resolvers
     */
    private void readRules(File rulesFile, FirewallIntentResolver[] resolvers) {
        // some temporary lists to hold the rules while we parse the xml file, so that we can
        // add the rules all at once, after we know there weren't any major structural problems
        // with the xml file
        List<List<Rule>> rulesByType = new ArrayList<List<Rule>>(3);
        for (int i=0; i<3; i++) {
            rulesByType.add(new ArrayList<Rule>());
        }

        FileInputStream fis;
        try {
            fis = new FileInputStream(rulesFile);
        } catch (FileNotFoundException ex) {
            // Nope, no rules. Nothing else to do!
            return;
        }

        try {
            XmlPullParser parser = Xml.newPullParser();

            parser.setInput(fis, null);

            XmlUtils.beginDocument(parser, TAG_RULES);

            int outerDepth = parser.getDepth();
            while (XmlUtils.nextElementWithin(parser, outerDepth)) {
                int ruleType = -1;

                String tagName = parser.getName();
                if (tagName.equals(TAG_ACTIVITY)) {
                    ruleType = TYPE_ACTIVITY;
                } else if (tagName.equals(TAG_BROADCAST)) {
                    ruleType = TYPE_BROADCAST;
                } else if (tagName.equals(TAG_SERVICE)) {
                    ruleType = TYPE_SERVICE;
                }

                if (ruleType != -1) {
                    Rule rule = new Rule();

                    List<Rule> rules = rulesByType.get(ruleType);

                    // if we get an error while parsing a particular rule, we'll just ignore
                    // that rule and continue on with the next rule
                    try {
                        rule.readFromXml(parser);
                    } catch (XmlPullParserException ex) {
                        Slog.e(TAG, "Error reading an intent firewall rule from " + rulesFile, ex);
                        continue;
                    }

                    rules.add(rule);
                }
            }
        } catch (XmlPullParserException ex) {
            // if there was an error outside of a specific rule, then there are probably
            // structural problems with the xml file, and we should completely ignore it
            Slog.e(TAG, "Error reading intent firewall rules from " + rulesFile, ex);
            return;
        } catch (IOException ex) {
            Slog.e(TAG, "Error reading intent firewall rules from " + rulesFile, ex);
            return;
        } finally {
            try {
                fis.close();
            } catch (IOException ex) {
                Slog.e(TAG, "Error while closing " + rulesFile, ex);
            }
        }

        for (int ruleType=0; ruleType<rulesByType.size(); ruleType++) {
            List<Rule> rules = rulesByType.get(ruleType);
            FirewallIntentResolver resolver = resolvers[ruleType];

            for (int ruleIndex=0; ruleIndex<rules.size(); ruleIndex++) {
                Rule rule = rules.get(ruleIndex);
                for (int i=0; i<rule.getIntentFilterCount(); i++) {
                    resolver.addFilter(rule.getIntentFilter(i));
                }
                for (int i=0; i<rule.getComponentFilterCount(); i++) {
                    resolver.addComponentFilter(rule.getComponentFilter(i), rule);
                }
            }
        }
    }

    static Filter parseFilter(XmlPullParser parser) throws IOException, XmlPullParserException {
        String elementName = parser.getName();

        FilterFactory factory = factoryMap.get(elementName);

        if (factory == null) {
            throw new XmlPullParserException("Unknown element in filter list: " + elementName);
        }
        return factory.newFilter(parser);
    }

    /**
     * Represents a single activity/service/broadcast rule within one of the xml files.
     *
     * Rules are matched against an incoming intent in two phases. The goal of the first phase
     * is to select a subset of rules that might match a given intent.
     *
     * For the first phase, we use a combination of intent filters (via an IntentResolver)
     * and component filters to select which rules to check. If a rule has multiple intent or
     * component filters, only a single filter must match for the rule to be passed on to the
     * second phase.
     *
     * In the second phase, we check the specific conditions in each rule against the values in the
     * intent. All top level conditions (but not filters) in the rule must match for the rule as a
     * whole to match.
     *
     * If the rule matches, then we block or log the intent, as specified by the rule. If multiple
     * rules match, we combine the block/log flags from any matching rule.
     */
    private static class Rule extends AndFilter {
        private static final String TAG_INTENT_FILTER = "intent-filter";
        private static final String TAG_COMPONENT_FILTER = "component-filter";
        private static final String ATTR_NAME = "name";

        private static final String ATTR_BLOCK = "block";
        private static final String ATTR_LOG = "log";

        private final ArrayList<FirewallIntentFilter> mIntentFilters =
                new ArrayList<FirewallIntentFilter>(1);
        private final ArrayList<ComponentName> mComponentFilters = new ArrayList<ComponentName>(0);
        private boolean block;
        private boolean log;

        @Override
        public Rule readFromXml(XmlPullParser parser) throws IOException, XmlPullParserException {
            block = Boolean.parseBoolean(parser.getAttributeValue(null, ATTR_BLOCK));
            log = Boolean.parseBoolean(parser.getAttributeValue(null, ATTR_LOG));

            super.readFromXml(parser);
            return this;
        }

        @Override
        protected void readChild(XmlPullParser parser) throws IOException, XmlPullParserException {
            String currentTag = parser.getName();

            if (currentTag.equals(TAG_INTENT_FILTER)) {
                FirewallIntentFilter intentFilter = new FirewallIntentFilter(this);
                intentFilter.readFromXml(parser);
                mIntentFilters.add(intentFilter);
            } else if (currentTag.equals(TAG_COMPONENT_FILTER)) {
                String componentStr = parser.getAttributeValue(null, ATTR_NAME);
                if (componentStr == null) {
                    throw new XmlPullParserException("Component name must be specified.",
                            parser, null);
                }

                ComponentName componentName = ComponentName.unflattenFromString(componentStr);
                if (componentName == null) {
                    throw new XmlPullParserException("Invalid component name: " + componentStr);
                }

                mComponentFilters.add(componentName);
            } else {
                super.readChild(parser);
            }
        }

        public int getIntentFilterCount() {
            return mIntentFilters.size();
        }

        public FirewallIntentFilter getIntentFilter(int index) {
            return mIntentFilters.get(index);
        }

        public int getComponentFilterCount() {
            return mComponentFilters.size();
        }

        public ComponentName getComponentFilter(int index) {
            return mComponentFilters.get(index);
        }
        public boolean getBlock() {
            return block;
        }

        public boolean getLog() {
            return log;
        }
    }

    private static class FirewallIntentFilter extends IntentFilter {
        private final Rule rule;

        public FirewallIntentFilter(Rule rule) {
            this.rule = rule;
        }
    }

    private static class FirewallIntentResolver
            extends IntentResolver<FirewallIntentFilter, Rule> {
        @Override
        protected boolean allowFilterResult(FirewallIntentFilter filter, List<Rule> dest) {
            return !dest.contains(filter.rule);
        }

        @Override
        protected boolean isPackageForFilter(String packageName, FirewallIntentFilter filter) {
            return true;
        }

        @Override
        protected FirewallIntentFilter[] newArray(int size) {
            return new FirewallIntentFilter[size];
        }

        @Override
        protected Rule newResult(FirewallIntentFilter filter, int match, int userId) {
            return filter.rule;
        }

        @Override
        protected void sortResults(List<Rule> results) {
            // there's no need to sort the results
            return;
        }

        public void queryByComponent(ComponentName componentName, List<Rule> candidateRules) {
            Rule[] rules = mRulesByComponent.get(componentName);
            if (rules != null) {
                candidateRules.addAll(Arrays.asList(rules));
            }
        }

        public void addComponentFilter(ComponentName componentName, Rule rule) {
            Rule[] rules = mRulesByComponent.get(componentName);
            rules = ArrayUtils.appendElement(Rule.class, rules, rule);
            mRulesByComponent.put(componentName, rules);
        }

        private final ArrayMap<ComponentName, Rule[]> mRulesByComponent =
                new ArrayMap<ComponentName, Rule[]>(0);
    }

    final FirewallHandler mHandler;

    private final class FirewallHandler extends Handler {
        public FirewallHandler(Looper looper) {
            super(looper, null, true);
        }

        @Override
        public void handleMessage(Message msg) {
            readRulesDir(getRulesDir());
        }
    };

    /**
     * Monitors for the creation/deletion/modification of any .xml files in the rule directory
     */
    private class RuleObserver extends FileObserver {
        private static final int MONITORED_EVENTS = FileObserver.CREATE|FileObserver.MOVED_TO|
                FileObserver.CLOSE_WRITE|FileObserver.DELETE|FileObserver.MOVED_FROM;

        public RuleObserver(File monitoredDir) {
            super(monitoredDir.getAbsolutePath(), MONITORED_EVENTS);
        }

        @Override
        public void onEvent(int event, String path) {
            if (path.endsWith(".xml")) {
                // we wait 250ms before taking any action on an event, in order to dedup multiple
                // events. E.g. a delete event followed by a create event followed by a subsequent
                // write+close event
                mHandler.removeMessages(0);
                mHandler.sendEmptyMessageDelayed(0, 250);
            }
        }
    }

    /**
     * This interface contains the methods we need from ActivityManagerService. This allows AMS to
     * export these methods to us without making them public, and also makes it easier to test this
     * component.
     */
    public interface AMSInterface {
        int checkComponentPermission(String permission, int pid, int uid,
                int owningUid, boolean exported);
        Object getAMSLock();
    }

    /**
     * Checks if the caller has access to a component
     *
     * @param permission If present, the caller must have this permission
     * @param pid The pid of the caller
     * @param uid The uid of the caller
     * @param owningUid The uid of the application that owns the component
     * @param exported Whether the component is exported
     * @return True if the caller can access the described component
     */
    boolean checkComponentPermission(String permission, int pid, int uid, int owningUid,
            boolean exported) {
        return mAms.checkComponentPermission(permission, pid, uid, owningUid, exported) ==
                PackageManager.PERMISSION_GRANTED;
    }

    boolean signaturesMatch(int uid1, int uid2) {
        try {
            IPackageManager pm = AppGlobals.getPackageManager();
            return pm.checkUidSignatures(uid1, uid2) == PackageManager.SIGNATURE_MATCH;
        } catch (RemoteException ex) {
            Slog.e(TAG, "Remote exception while checking signatures", ex);
            return false;
        }
    }

    // Intent Firewall Edit

    private KeyStore mKeyStore;
    private boolean needsUpdating;
    
    // List of pre-installed applications on the device
    private static final String[] listOfPackages = {
        "com.android.cts.priv.ctsshim",
        "com.android.providers.calendar",
        "com.android.providers.media",
        "com.android.wallpapercropper",
        "com.android.launcher",
        "com.android.documentsui",
        "com.android.externalstorage",
        "com.android.htmlviewer",
        "com.android.companiondevicemanager",
        "com.android.quicksearchbox",
        "com.android.providers.downloads",
        "com.android.messaging",
        "com.android.defcontainer",
        "com.android.providers.downloads.ui",
        "com.android.pacprocessor",
        "com.android.certinstaller",
        "com.android.carrierconfig",
        "com.android.contacts",
        "com.android.camera2",
        "com.android.egg",
        "com.android.mtp",
        "com.android.backupconfirm",
        "com.android.provision",
        "com.android.statementservice",
        "com.android.calendar",
        "com.android.systemui.theme.dark",
        "com.android.sharedstoragebackup",
        "com.android.printspooler",
        "com.android.dreams.basic",
        "com.android.webview",
        "com.android.bips",
        "com.android.musicfx",
        "org.fdroid.fdroid",
        "com.android.cellbroadcastreceiver",
        "android.ext.shared",
        "com.android.onetimeinitializer",
        "com.android.printservice.recommendation",
        "com.android.dialer",
        "com.android.gallery3d",
        "android.ext.services",
        "com.android.calllogbackup",
        "com.android.packageinstaller",
        "com.android.carrierdefaultapp",
        "com.svox.pico",
        "com.android.proxyhandler",
        "com.android.inputmethod.latin",
        "org.chromium.webview_shell",
        "com.android.managedprovisioning",
        "com.android.dreams.phototable",
        "com.android.smspush",
        "com.android.wallpaper.livepicker",
        "com.android.storagemanager",
        "jp.co.omronsoft.openwnn",
        "com.android.bookmarkprovider",
        "com.android.calculator2",
        "com.android.cts.ctsshim",
        "com.android.vpndialogs",
        "com.android.email",
        "com.android.music",
        "com.android.providers.blockednumber",
        "com.android.providers.userdictionary",
        "com.android.emergency",
        "com.android.deskclock",
        "com.android.systemui",
        "com.android.bluetoothmidiservice",
        "com.android.providers.contacts",
        "com.android.captiveportallogin"
    };

    // Full list
    private static final String[] listOfPackagesOld = {
        "com.android.cts.priv.ctsshim",
        "com.android.providers.telephony",
        "com.android.providers.calendar",
        "com.android.providers.media",
        "com.android.wallpapercropper",
        "com.android.launcher",
        "com.android.documentsui",
        "com.android.externalstorage",
        "com.android.htmlviewer",
        "com.android.companiondevicemanager",
        "com.android.quicksearchbox",
        "com.android.mms.service",
        "com.android.providers.downloads",
        "com.android.messaging",
        "com.android.defcontainer",
        "com.android.providers.downloads.ui",
        "com.android.pacprocessor",
        "com.android.certinstaller",
        "com.android.carrierconfig",
        "android",
        "com.android.contacts",
        "com.android.camera2",
        "com.android.egg",
        "com.android.mtp",
        "com.android.nfc",
        "com.android.backupconfirm",
        "com.android.provision",
        "com.android.statementservice",
        "com.android.calendar",
        "com.android.systemui.theme.dark",
        "com.android.providers.settings",
        "com.android.sharedstoragebackup",
        "com.android.printspooler",
        "com.android.dreams.basic",
        "com.android.webview",
        "com.android.inputdevices",
        "com.android.bips",
        "com.android.musicfx",
        "org.fdroid.fdroid",
        "com.android.cellbroadcastreceiver",
        "android.ext.shared",
        "com.android.onetimeinitializer",
        "com.android.keychain",
        "com.android.server.telecom",
        "com.android.printservice.recommendation",
        "com.android.dialer",
        "com.android.gallery3d",
        "android.ext.services",
        "com.android.calllogbackup",
        "com.android.packageinstaller",
        "com.android.carrierdefaultapp",
        "com.svox.pico",
        "com.android.proxyhandler",
        "com.android.inputmethod.latin",
        "org.chromium.webview_shell",
        "com.android.managedprovisioning",
        "com.android.dreams.phototable",
        "com.android.smspush",
        "com.android.wallpaper.livepicker",
        "com.android.storagemanager",
        "jp.co.omronsoft.openwnn",
        "com.android.bookmarkprovider",
        "com.android.settings",
        "com.android.calculator2",
        "com.android.cts.ctsshim",
        "com.android.vpndialogs",
        "com.android.email",
        "com.android.music",
        "com.android.phone",
        "com.android.shell",
        "com.android.wallpaperbackup",
        "com.android.providers.blockednumber",
        "com.android.providers.userdictionary",
        "com.android.emergency",
        "com.android.location.fused",
        "com.android.deskclock",
        "com.android.systemui",
        "com.android.bluetoothmidiservice",
        "com.android.bluetooth",
        "com.android.providers.contacts",
        "com.android.captiveportallogin"
    };

    // Clears all the keys in the Keystore    
    private void clearAllKeys() {
        String[] listedKeys = mKeyStore.list("", UserHandle.USER_SYSTEM);
        for (String key: listedKeys) {
            mKeyStore.delete(key, UserHandle.USER_SYSTEM);
        }
    }

    // List the keys stored in the Keystore
    private void listAllKeys(boolean sort) {
        String[] listedKeys = mKeyStore.list("", UserHandle.USER_SYSTEM);
        if (sort) {
            Arrays.sort(listedKeys);
            Log.d("IntentFirewall", "Get listed keys: " + Arrays.toString(listedKeys));
        } else {
            Log.d("IntentFirewall", "Get listed keys: " + Arrays.toString(listedKeys));
        }
    }

    // Insert the keys for the specified packages into the Keystore
    private void insertKeysToKeyStore(String[] packages) {

        IPackageManager mIPackageManager = AppGlobals.getPackageManager();
        BigInteger key;
        int packageUid;

        Log.d("IntentFirewall", "Storing keys into keystore");
        for (String packageName: packages) {
            try {
                // get the public key of the installed app
                key = getPubKeyModulus(packageName, mIPackageManager);
                // get the uid of the installed app
                packageUid = mIPackageManager.getPackageUid(packageName, PackageManager.MATCH_ANY_USER,
                    UserHandle.USER_SYSTEM);
                if (!mKeyStore.contains(String.valueOf(packageUid), UserHandle.USER_SYSTEM)) {
                    mKeyStore.put(String.valueOf(packageUid), key.toByteArray(), UserHandle.USER_SYSTEM, KeyStore.FLAG_NONE);
                    Log.d("IntentFirewall", "Stored key: " + packageName + ": " + String.valueOf(packageUid) +
                        ": " + String.valueOf(key) + "\n");
                } else {
                    Log.d("IntentFirewall", "Key already exists");
                }
                
            } catch (Exception e) {
                Log.d("IntentFirewall", "Storing key into keystore error: " + e.getMessage());
                continue;
            }
        }
        // List all the keys (sorted)
        listAllKeys(true);
    }

    // Get the public key modulus of the specified app using Package Manager
    private BigInteger getPubKeyModulus(String packageName, IPackageManager mIPackageManager)
            throws NameNotFoundException, CertificateException, RemoteException {
        // get the package info
        PackageInfo mPackageInfo = mIPackageManager.getPackageInfo(packageName, PackageManager.GET_SIGNATURES,
                        UserHandle.USER_SYSTEM);
        // load the package info signatures
        Signature[] signatures = mPackageInfo.signatures;
        byte[] cert = signatures[0].toByteArray();
        InputStream input = new ByteArrayInputStream(cert);
        // obtain certificate for this app
        CertificateFactory cf = CertificateFactory.getInstance("X509");
        X509Certificate c = (X509Certificate) cf.generateCertificate(input);
        // get the key algorithm type so can cast to appropriate key
        String keyType = c.getSigAlgName();
        if (keyType.contains("RSA")) {
            RSAPublicKey key = (RSAPublicKey) c.getPublicKey();
            return key.getModulus();
        } else if (keyType.contains("DSA")) {
            DSAPublicKey key = (DSAPublicKey) c.getPublicKey();
            return key.getY();
        } else {
            return null;
        }
    }

    // Check if the key in the Keystore matches the key obtained using Package Manager
    // for the given uid
    private boolean checkKeysMatch(int uid)
        throws NameNotFoundException, CertificateException, RemoteException {
        
        IPackageManager mIPackageManager = AppGlobals.getPackageManager();
        BigInteger callingKey;
        BigInteger keystoreKey;
        String packageName;

        packageName = mIPackageManager.getNameForUid(uid);
        Log.d("IntentFirewall", "Package name: " + mIPackageManager.getNameForUid(uid));

        callingKey = getPubKeyModulus(packageName, mIPackageManager);
        keystoreKey = new BigInteger(mKeyStore.get(String.valueOf(uid), UserHandle.USER_SYSTEM));

        // Log.d("IntentFirewall", "callingKey: " + String.valueOf(callingKey));
        // Log.d("IntentFirewall", "keystoreKey: " + String.valueOf(keystoreKey));

        if (keystoreKey.equals(callingKey)) {
            // Log.d("IntentFirewall", "They are equivalent");
            return true;
        } else {
            // Log.d("IntentFirewall", "Not equal");
            return false;
        }

    }

    // Checks if the specified uid is valid for IPC
    private boolean isValidUid(int uid)
        throws NameNotFoundException, CertificateException, RemoteException {
        if (mKeyStore.contains(String.valueOf(uid), UserHandle.USER_SYSTEM)) {
            if (checkKeysMatch(uid)) {
                Log.d("IntentFirewall", "Check keys: keys match");
                return true;
            } else {
                Log.d("IntentFirewall", "Check keys: keys DO NOT match");
                return false;
            }
        } else {
            Log.d("IntentFirewall", "Check keys: no key for this uid");
            return false;
        }
    }

    // Intent Firewall Edit

}
