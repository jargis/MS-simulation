/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package finalsim;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Random;
import javafx.util.Pair;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.LinkedList;
import java.util.List;

import org.cloudbus.cloudsim.Cloudlet;
import org.cloudbus.cloudsim.CloudletSchedulerSpaceShared;
import org.cloudbus.cloudsim.CloudletSchedulerTimeShared;
import org.cloudbus.cloudsim.Datacenter;
import org.cloudbus.cloudsim.DatacenterBroker;
import org.cloudbus.cloudsim.DatacenterCharacteristics;
import org.cloudbus.cloudsim.Host;
import org.cloudbus.cloudsim.Log;
import org.cloudbus.cloudsim.Pe;
import org.cloudbus.cloudsim.Storage;
import org.cloudbus.cloudsim.UtilizationModel;
import org.cloudbus.cloudsim.UtilizationModelFull;
import org.cloudbus.cloudsim.Vm;
import org.cloudbus.cloudsim.VmAllocationPolicySimple;
import org.cloudbus.cloudsim.VmSchedulerTimeShared;
import org.cloudbus.cloudsim.core.CloudSim;
import org.cloudbus.cloudsim.provisioners.BwProvisionerSimple;
import org.cloudbus.cloudsim.provisioners.PeProvisionerSimple;
import org.cloudbus.cloudsim.provisioners.RamProvisionerSimple;

/**
 *
 * @author Jargis
 */
class ESP {

    int ESP_ID;
    int q, qGet, qA;
    double lambda, Tth, mu; // 0.5 per ms
    double alpha = 20.0, beta = 0.01, gamma = 0.001, theta = 1.0 / 50.0;
    double dis[];
    double r[];
    double totUtil;
    int mecID;
    boolean noF = false;
    boolean C = false;

    ESP(int id, double d[], double R[]) {
        dis = d;
        r = R;
        ESP_ID = id;
    }

    void calcUtil() {

        double z = (double) mu - (double) lambda / (double) qGet;
        System.out.println("Here in normal z = " + z);
        double d;
        if (z <= 0) {
            d = Tth;
        } else {
            d = (double) lambda / z;
        }

        double t = (double) dis[mecID] * (double) theta + d;// + Tth;
        System.out.println("ID = " + ESP_ID + " t val = " + t + " where MEC = " + mecID + " " + dis[mecID] + " d= " + d);
        totUtil = alpha * (double) lambda - (double) beta * (double) qGet * (double) r[mecID] - (double) gamma * t;
    }
}

class pair {

    int ID;
    double p;

    pair(int a, double b) {
        ID = a;
        p = b;
    }

    public String toString() {
        return "" + ID + " " + p;
    }
}

class MEC {

    int ID;
    boolean b_s;    /// true for seller, false for buyer
    int crbMEC, initCRB;
    int Q;
    int q0;
    int qb;
    int reqCRB;
    int eavCRB;
    double e;
    int p[];
    int tR;
    int cdelay[];
    int frmSeller;
    double utilMEC;
    double utilSel;
    double cccc;
    double dddd;
    double eCost;
    ArrayList<pair> ServESP;
    ArrayList<pair> LB;  // List of buyers if this MEC is a seller
    ArrayList<pair> LS;  // List of sellers if this MEC is a Buyer
    ArrayList<pair> LBPref = new ArrayList<pair>();

    ArrayList<Integer> MD = new ArrayList<Integer>();
    int minPforESPs;

    MEC(int i, boolean f, int c, double ee) {
        ID = i;
        b_s = f;
        initCRB = crbMEC = c;
        eCost = ee;
    }

}

class St {

    ArrayList<ESP> allESP = new ArrayList<ESP>();
    ArrayList<MEC> allMEC = new ArrayList<MEC>();
    ArrayList<MEC> allSeller = new ArrayList<MEC>();
    ArrayList<MEC> allBuyer = new ArrayList<MEC>();
//    ArrayList<IC> allIC = new ArrayList<IC>();
    int NoESP = 200;
    int NoMEC = 5;
    int BasePrice = 2;
    double lambda = 0.8; // 0.5 per ms
    double alpha = 20.0, beta = 0.01, gamma = 0.001, theta = 1.0 / 50.0, mu = .1;
    double Tth = 60;
    String F_name = "SBG_ld_800.txt";
    //&&&&&&&&&&&&&&&&&&&&&&&&
    double slambda = 800; // 0.5 per ms
    double salpha = 20.0 / 1000.0, sbeta = 0.01 / 1000.0, sgamma = 0.001 / 1000.0, stheta = 1.0 / 50.0, smu = 100.0;
    double sTth = 60.0 / 1000.0;
    //&&&&&&&&&&&&&&&&&&&&&&&&
    double acpu;
    int ac;
    double wt;
    double price;
    int DisMEC[][];      // communication delay MEC--MEC
    int cDelayIC[][];       // communication delay MEC--IC
    int conESParr[] = new int[NoESP];
    ArrayList<Integer> ESP_MEC = new ArrayList<Integer>();
    int itr;

    St(int i) throws IOException {
        itr = i;
        Init();
        //print();
        otm();
        espUtilCal();
        printUtilVal();
    }

    void Init() {
        double min_Q = 0;
        double max_R = 0;

        double smin_Q = (slambda * sTth) / (smu * sTth - slambda);
        double smax_R = (sgamma / sbeta) * Math.pow((smu * sTth - slambda) / slambda, 2);
        double soptQ = (slambda / smu) * (1.0 + Math.sqrt(sgamma / smax_R / sbeta));
        double DQ = (double) mu - (double) lambda / (double) soptQ;

        min_Q = soptQ;
        max_R = smax_R * 100;
        System.out.println("Herrrrrrrrrrrrrrrrrrrrrrrrrreeeeeeeeeeeeeeeeeeeeeeee  MaxR = " + max_R + " OptQ " + min_Q);
        DisMEC = new int[NoMEC][NoMEC];

        for (int i = 0; i < NoMEC; i++) // MEC-MEC delay
        {
            for (int j = 0; j < NoMEC; j++) {
                if (i == j) {
                    continue;
                }
                Random r = new Random();
                DisMEC[i][j] = r.nextInt(30) + 20;
            }
        }

        price = max_R;
        for (int i = 0; i < NoESP; i++) // Storing info of ESPS
        {
            double d[] = new double[NoMEC];     // distance
            double R[] = new double[NoMEC];       // price
            for (int j = 0; j < NoMEC; j++) {
                Random r = new Random();
                d[j] = (double) (r.nextInt(10) + 1);
                R[j] = (double) r.nextInt(4) + (max_R - 1.0);
            }
            allESP.add(new ESP(i, d, R));
        }
        int espCnt = 0;
        for (int i = 0; i < NoESP; i++) {
            conESParr[i] = -1;
        }
        for (int x = 0; x < NoESP; x++) {
            double min = 99999;
            int id = 0;
            for (int y = 0; y < NoMEC; y++) {
                if (allESP.get(x).r[y] <= min) {
                    min = allESP.get(x).r[y];
                    id = y;
                }
            }
            //Random d = new Random();
            //int z = d.nextInt(NoMEC);
            conESParr[x] = id;
        }
        int ESPcrbCNT = 0;
        for (int i = 0; i < allESP.size(); i++) {
            int temp = (int) ((int) (slambda / smu) * (1.0 + Math.sqrt(sgamma / smax_R / sbeta)));
            allESP.get(i).q = allESP.get(i).qA = temp;
            allESP.get(i).lambda = slambda / 1000;
            allESP.get(i).mu = smu / 1000;
            allESP.get(i).Tth = sTth * 1000;
            ESPcrbCNT += temp;
        }

        int cntCRB = 0;
        for (int i = 0; i < NoMEC; i++) {
            boolean f = false;
            Random br = new Random();

            int crb;
            crb = br.nextInt(200) + 400;
            cntCRB += crb;
            double ee = br.nextInt(3) + 2;
            allMEC.add(new MEC(i, f, crb, ee));
        }
        System.out.println("MEC tot crb = " + cntCRB + " ESP tot crb = " + ESPcrbCNT);

        for (int i = 0; i < NoMEC; i++) {
            ArrayList<pair> temp = new ArrayList<pair>();
            for (int j = 0; j < NoESP; j++) {
                if (conESParr[j] == i) {
                    temp.add(new pair(j, allESP.get(j).r[i]));
                }
            }
            allMEC.get(i).ServESP = temp;
        }
    }
    ArrayList<Integer> SystemSE = new ArrayList<Integer>();
    ArrayList<Integer> SystemBU = new ArrayList<Integer>();

    ArrayList<ArrayList<Integer>> PriceFSell = new ArrayList<ArrayList<Integer>>();

    int delayFbs[][];
    int priceFbs[][];

    double PrefCalBuy(int bN, int sN) {
        int Pmax = -1, Pmin = 999999;
        int Dmax = -1, Dmin = 999999;
        double Nprice, Ndelay, pZeta = .9, dIta = .3;
        for (int j = 0; j < SystemSE.size(); j++) {
            if (delayFbs[bN][j] > Dmax) {
                Dmax = delayFbs[bN][j];
            }
            if (delayFbs[bN][j] < Dmin) {
                Dmin = delayFbs[bN][j];
            }
            if (priceFbs[bN][j] > Pmax) {
                Pmax = priceFbs[bN][j];
            }
            if (priceFbs[bN][j] < Pmin) {
                Pmin = priceFbs[bN][j];
            }
        }
        if (Pmax == Pmin) {
            Nprice = 1;
        } else {
            Nprice = (double) (priceFbs[bN][sN] - Pmin) / (double) (Pmax - Pmin);
        }
        if (Dmax == Dmin) {
            Ndelay = 1;
        } else {
            Ndelay = (double) (delayFbs[bN][sN] - Dmin) / (double) (Dmax - Dmin);
        }

        return Nprice * pZeta + Ndelay * dIta;
    }

    void setDelay() {
        Random r = new Random();
        for (int i = 0; i < SystemBU.size(); i++) {
            System.out.println("Communication delay for Buyer " + SystemBU.get(i));
            for (int j = 0; j < SystemSE.size(); j++) {
                delayFbs[i][j] = r.nextInt(200);
                System.out.println("seller " + SystemSE.get(j) + " - " + delayFbs[i][j] + "ms");
            }
        }
    }

    void setPrice() {       // buyer in rows and sellers in column. buyer keeps track of the price set by seller
        Random r = new Random();
        for (int i = 0; i < SystemBU.size(); i++) {
            System.out.println("Pricing for Buyer " + SystemBU.get(i));
            for (int j = 0; j < SystemSE.size(); j++) {
                if (price > 50) {
                    priceFbs[i][j] = r.nextInt((int) 30) + (int) (price - 50);
                } else {
                    //priceFbs[i][j] = (int) (r.nextInt((int) price/4) + price/4);
                    priceFbs[i][j] = r.nextInt((int) price);
                }
                System.out.println("seller " + SystemSE.get(j) + " - " + priceFbs[i][j] + "$");
            }
        }
    }

    void mtm() {

        for (int i = 0; i < allMEC.size(); i++) {
            if (allMEC.get(i).b_s) // construct seller pref
            {
                SystemSE.add(allMEC.get(i).ID);
            } else {
                SystemBU.add(allMEC.get(i).ID);
            }
        }
        delayFbs = new int[SystemBU.size()][SystemSE.size()];
        priceFbs = new int[SystemBU.size()][SystemSE.size()];
        setDelay();
        setPrice();
        System.out.print("List of seller =");       // printing list of buyer and seller
        for (int i = 0; i < SystemSE.size(); i++) {
            System.out.println("MEC ID " + SystemSE.get(i) + " CRBs = " + allMEC.get(SystemSE.get(i)).crbMEC);
        }
        System.out.println();
        System.out.print("List of Buyer =");
        for (int i = 0; i < SystemBU.size(); i++) {
            System.out.println("MEC ID " + SystemBU.get(i) + " CRBs = " + allMEC.get(SystemBU.get(i)).crbMEC);
        }
        System.out.println();

        /*for (int i = 0; i < SystemSE.size(); i++) {
            ArrayList<pair> ts = new ArrayList<pair>();
            for (int j = 0; j < SystemBU.size(); j++) {
                //Random rnd = new Random();
                //int temp = rnd.nextInt(3) + 2;
                pair prB = new pair(SystemBU.get(j), priceFbs[j][i]);
                ts.add(prB);
                //allMEC.get(SystemSE.get(i)).LB.add(prB);
            }
            allMEC.get(SystemSE.get(i)).LB = ts;
        }*/
        for (int i = 0; i < SystemBU.size(); i++) {
            ArrayList<pair> bs = new ArrayList<pair>();
            for (int j = 0; j < SystemSE.size(); j++) {
                //Random rnd = new Random();
                //int temp = rnd.nextInt(100) + 200;
                pair prB = new pair(SystemSE.get(j), PrefCalBuy(i, j));
                bs.add(prB);
                //allMEC.get(SystemBU.get(i)).LS.add(prB);
            }
            allMEC.get(SystemBU.get(i)).LS = bs;
        }
        /*System.out.println("here comes the list + " + SystemSE.size());
        for (int i = 0; i < SystemSE.size(); i++) {
            int size = allMEC.get(SystemSE.get(i)).LB.size();

            System.out.println("size = " + size);
            for (int j = 0; j < size; j++) {
                System.out.println("Seller " + SystemSE.get(i) + " list of buyer = " + allMEC.get(SystemSE.get(i)).LB.get(j).ID + " " + allMEC.get(SystemSE.get(i)).LB.get(j).p);
            }
        }*/
        for (int i = 0; i < SystemBU.size(); i++) {
            int size = allMEC.get(SystemBU.get(i)).LS.size();

            System.out.println("size = " + size);
            for (int j = 0; j < size; j++) {
                System.out.println("Buyer " + SystemBU.get(i) + " list = " + allMEC.get(SystemBU.get(i)).LS.get(j).ID + " " + allMEC.get(SystemBU.get(i)).LS.get(j).p);
            }
        }
        /*for (int i = 0; i < SystemSE.size(); i++) {
            Collections.sort(allMEC.get(SystemSE.get(i)).LB, new Comparator<pair>() {
                @Override
                public int compare(pair p1, pair p2) {
                    //return p2.p - p1.p;
                    return Double.compare(p2.p, p1.p);
                }
            });
        }*/
        //ascending order sort
        for (int i = 0; i < SystemBU.size(); i++) {
            Collections.sort(allMEC.get(SystemBU.get(i)).LS, new Comparator<pair>() {
                @Override
                public int compare(pair p1, pair p2) {
                    //return p2.p - p1.p;
                    return Double.compare(p2.p, p1.p);
                }
            });
        }
        System.out.println("After sorting");
        /*for (int i = 0; i < SystemSE.size(); i++) {
            int size = allMEC.get(SystemSE.get(i)).LB.size();

            System.out.println("size = " + size);
            for (int j = 0; j < size; j++) {
                System.out.println("Seller " + SystemSE.get(i) + " list of buyer = " + allMEC.get(SystemSE.get(i)).LB.get(j).ID + " " + allMEC.get(SystemSE.get(i)).LB.get(j).p);
            }
        }*/
        for (int i = 0; i < SystemBU.size(); i++) {
            int size = allMEC.get(SystemBU.get(i)).LS.size();

            System.out.println("size = " + size);
            for (int j = 0; j < size; j++) {
                System.out.println("Buyer " + SystemBU.get(i) + " list = " + allMEC.get(SystemBU.get(i)).LS.get(j).ID + " " + allMEC.get(SystemBU.get(i)).LS.get(j).p);
            }
        }
        Random c_s = new Random();
/////////////////////////////////////////// new tech
        for (int i = 0; i < SystemBU.size(); i++) {
            int size = SystemSE.size();
            for (int j = 0; j < size; j++) {
                double tV = priceFbs[i][SystemSE.indexOf(allMEC.get(SystemBU.get(i)).LS.get(j).ID)];
                int pS = allMEC.get(SystemBU.get(i)).LS.get(j).ID;
                allMEC.get(pS).LBPref.add(new pair(SystemBU.get(i), tV));
            }
        }
        for (int j = 0; j < SystemSE.size(); j++) {
            Collections.sort(allMEC.get(SystemSE.get(j)).LBPref, new Comparator<pair>() {
                @Override
                public int compare(pair p1, pair p2) {
                    //return p2.p - p1.p;
                    return Double.compare(p2.p, p1.p);
                }
            });
        }
        int sel_seller[] = new int[SystemSE.size()];
        for (int k = 0; k < SystemSE.size(); k++) {
            int seller = SystemSE.get(k);
            //assign untill resource left
            for (int w = 0; w < allMEC.get(seller).LBPref.size(); w++) {
                if (allMEC.get(seller).eavCRB != 0) {
                    if (allMEC.get(seller).eavCRB > allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB && allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB != 0) {
                        System.out.println("Seller " + seller + " providing " + allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB + " CRBs to buyer " + allMEC.get(seller).LBPref.get(w).ID);
                        allMEC.get(seller).eavCRB -= allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB;
                        allMEC.get(allMEC.get(seller).LBPref.get(w).ID).frmSeller += allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB;

                        // delay input
                        allMEC.get(allMEC.get(seller).LBPref.get(w).ID).MD.add(seller);
                        //$$$$$$$$$$$$$$ impose utility functions equation (6)
                        System.out.println("Checking error actual buyer = " + allMEC.get(seller).LBPref.get(w).ID + " index in b_list " + SystemBU.indexOf(allMEC.get(seller).LBPref.get(w).ID) + " seller is " + seller);
                        allMEC.get(seller).utilSel += allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB * (priceFbs[SystemBU.indexOf(allMEC.get(seller).LBPref.get(w).ID)][SystemSE.indexOf(seller)] - price / 10.0);

                        /// buyer utility deduction as buying
                        allMEC.get(allMEC.get(seller).LBPref.get(w).ID).utilMEC -= allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB * priceFbs[SystemBU.indexOf(allMEC.get(seller).LBPref.get(w).ID)][SystemSE.indexOf(seller)] - DisMEC[allMEC.get(seller).LBPref.get(w).ID][seller] / 500;
                        allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB = 0;
                    } else if (allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB != 0) {
                        System.out.println("Seller " + seller + " providing " + allMEC.get(seller).eavCRB + " CRBs to buyer " + allMEC.get(seller).LBPref.get(w).ID);
                        allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB -= allMEC.get(seller).eavCRB;
                        allMEC.get(allMEC.get(seller).LBPref.get(w).ID).frmSeller += allMEC.get(seller).eavCRB;

                        // delay 
                        allMEC.get(allMEC.get(seller).LBPref.get(w).ID).MD.add(seller);
                        //$$$$$$$$$$$$$$ impose utility functions equation (6)
                        allMEC.get(seller).utilSel += allMEC.get(seller).eavCRB * (priceFbs[SystemBU.indexOf(allMEC.get(seller).LBPref.get(w).ID)][SystemSE.indexOf(seller)] - price / 10.0);

                        /// buyer utility deduction as buying
                        allMEC.get(allMEC.get(seller).LBPref.get(w).ID).utilMEC -= allMEC.get(allMEC.get(seller).LBPref.get(w).ID).reqCRB * priceFbs[SystemBU.indexOf(allMEC.get(seller).LBPref.get(w).ID)][SystemSE.indexOf(seller)] - DisMEC[allMEC.get(seller).LBPref.get(w).ID][seller] / 50;

                        allMEC.get(seller).eavCRB = 0;
                    }
                }
            }
        }
//////////////////////////// end new tech
    }

    void otm() {
        double eCost = 0;
        for (int i = 0; i < NoMEC; i++) {
            int required = 0;
            for (int j = 0; j < allMEC.get(i).ServESP.size(); j++) {
                required += allESP.get(allMEC.get(i).ServESP.get(j).ID).q;
                //required += allESP.get(i).q;
            }
            int check = required - allMEC.get(i).crbMEC;
            allMEC.get(i).tR = required;
            if (check < 0) {
                allMEC.get(i).eavCRB = -check;
                System.out.println("Requested CRBs to MEC " + i + " = " + required + " extra available = " + (-check) + " Seller");
                allMEC.get(i).b_s = true;   /// true for seller
            } else if (check > 0) {
                allMEC.get(i).reqCRB = check;
                allMEC.get(i).b_s = false;  /// false for buyer
                System.out.println("Requested CRBs to MEC " + i + " = " + required + " extra required = " + check + " Buyer");
            } else {
                System.out.println("Requested CRBs to MEC " + i + " = " + required + " extra required = " + check + " not buyer or seller");
            }
        }
        /////// run the many to many matching after getting requests form ESPs
        /////// also make sure that the allocation occured before the One to Many actual assignment
        mtm();
        for (int i = 0; i < allMEC.size(); i++) {
            MECSt(i);
        }

        // allocate CRBs to ESPs
        for (int i = 0; i < allMEC.size(); i++) {
            for (int j = 0; j < allMEC.get(i).ServESP.size(); j++) {
                Collections.sort(allMEC.get(i).ServESP, new Comparator<pair>() {
                    @Override
                    public int compare(pair p1, pair p2) {
                        //return p2.p - p1.p;
                        return Double.compare(p2.p, p1.p);
                    }
                });
            }
        }
        for (int i = 0; i < allMEC.size(); i++) {
            System.out.println("MEC no. preference is = " + i);
            for (int j = 0; j < allMEC.get(i).ServESP.size(); j++) {
                System.out.print("" + allMEC.get(i).ServESP.get(j).toString() + "*");
            }
            System.out.println();
        }
        /// creating cloudsim vms and cloudlet for simulation

        int checkCRBs = 0;
        for (int i = 0; i < allMEC.size(); i++) {

            if (allMEC.get(i).b_s) // seller allocates resources to its own ESPs
            {

                if (allMEC.get(i).crbMEC != 0) {
                    for (int j = 0; j < allMEC.get(i).ServESP.size(); j++) {
                        if (allESP.get(allMEC.get(i).ServESP.get(j).ID).q != 0 && allMEC.get(i).crbMEC >= allESP.get(allMEC.get(i).ServESP.get(j).ID).q) {
                            checkCRBs += allESP.get(allMEC.get(i).ServESP.get(j).ID).q;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet = allESP.get(allMEC.get(i).ServESP.get(j).ID).q;
                            allMEC.get(i).crbMEC -= allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).q = 0;
                            System.out.println("From Seller MEC " + i + " own ESP " + allMEC.get(i).ServESP.get(j).ID + " CRB got = " + allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet);
                            ////$$$$$$$$$$$ seller will also calculate its utility by serving ESP
                            allMEC.get(i).utilMEC += allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet * allESP.get(allMEC.get(i).ServESP.get(j).ID).r[i] - allMEC.get(i).cccc * allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet - 0.5 * allMEC.get(i).eCost * allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).mecID = allMEC.get(i).ID;
                        } else if (allESP.get(allMEC.get(i).ServESP.get(j).ID).q != 0 && allMEC.get(i).crbMEC < allESP.get(allMEC.get(i).ServESP.get(j).ID).q && allMEC.get(i).crbMEC != 0) {
                            // allocation of own CRB remaining
                            checkCRBs += allMEC.get(i).crbMEC;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet = allMEC.get(i).crbMEC;
                            allMEC.get(i).crbMEC = 0;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).q -= allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet;
                            System.out.println("From Seller MEC " + i + " own ESP " + allMEC.get(i).ServESP.get(j).ID + " fraction CRB got = " + allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet);
                            //// $$$$$ buyer utility for ESP
                            allMEC.get(i).utilMEC += allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet * allESP.get(allMEC.get(i).ServESP.get(j).ID).r[i] - allMEC.get(i).cccc * allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet - 0.5 * allMEC.get(i).eCost * allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).mecID = allMEC.get(i).ID;
                        }
                    }

                }
            } else {        // each buyer allocates CRBs to its own ESPs
                if (allMEC.get(i).crbMEC != 0) {
                    for (int j = 0; j < allMEC.get(i).ServESP.size(); j++) {
                        if (allESP.get(allMEC.get(i).ServESP.get(j).ID).q != 0 && allMEC.get(i).crbMEC >= allESP.get(allMEC.get(i).ServESP.get(j).ID).q) {
                            // allocation of own CRB
                            checkCRBs += allESP.get(allMEC.get(i).ServESP.get(j).ID).q;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet = allESP.get(allMEC.get(i).ServESP.get(j).ID).q;
                            allMEC.get(i).crbMEC -= allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).q = 0;
                            System.out.println("From Buyer MEC " + i + " own ESP " + allMEC.get(i).ServESP.get(j).ID + " CRB got = " + allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet);
                            //// $$$$$ buyer utility for ESP
                            allMEC.get(i).utilMEC += allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet * allESP.get(allMEC.get(i).ServESP.get(j).ID).r[i] - allMEC.get(i).cccc * allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet - 0.5 * allMEC.get(i).eCost * allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet;//- eCost;

                            allESP.get(allMEC.get(i).ServESP.get(j).ID).mecID = allMEC.get(i).ID;
                        } else if (allESP.get(allMEC.get(i).ServESP.get(j).ID).q != 0 && allMEC.get(i).crbMEC < allESP.get(allMEC.get(i).ServESP.get(j).ID).q && allMEC.get(i).crbMEC != 0) {
                            // allocation of own CRB remaining
                            checkCRBs += allMEC.get(i).crbMEC;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet = allMEC.get(i).crbMEC;
                            allMEC.get(i).crbMEC = 0;
                            allESP.get(allMEC.get(i).ServESP.get(j).ID).q -= allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet;
                            System.out.println("From Buyer MEC " + i + " own ESP " + allMEC.get(i).ServESP.get(j).ID + " fraction CRB got = " + allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet);
                            //// $$$$$ buyer utility for ESP
                            allMEC.get(i).utilMEC += allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet * allESP.get(allMEC.get(i).ServESP.get(j).ID).r[i] - allMEC.get(i).cccc * allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet - 0.5 * allMEC.get(i).eCost * allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet;//- eCost;

                            allESP.get(allMEC.get(i).ServESP.get(j).ID).mecID = allMEC.get(i).ID;
                        }
                        // buyer allocating resources bought from seller
                        if (allMEC.get(i).crbMEC == 0 && allMEC.get(i).frmSeller != 0) {
                            if (allESP.get(allMEC.get(i).ServESP.get(j).ID).q <= allMEC.get(i).frmSeller) {
                                // allocation of CRB bought from seller
                                checkCRBs += allESP.get(allMEC.get(i).ServESP.get(j).ID).q;
                                allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet += allESP.get(allMEC.get(i).ServESP.get(j).ID).q;
                                allMEC.get(i).frmSeller -= allESP.get(allMEC.get(i).ServESP.get(j).ID).q;
                                allESP.get(allMEC.get(i).ServESP.get(j).ID).q = 0;
                                System.out.println("From Buyer MEC " + i + " own ESP " + allMEC.get(i).ServESP.get(j).ID + " from seller CRB got = " + allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet);
                                //// $$$$$ buyer utility for ESP
                                allMEC.get(i).utilMEC += allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet * allESP.get(allMEC.get(i).ServESP.get(j).ID).r[i];

                                allESP.get(allMEC.get(i).ServESP.get(j).ID).mecID = allMEC.get(i).ID;
                            } else if (allESP.get(allMEC.get(i).ServESP.get(j).ID).q > allMEC.get(i).frmSeller) {
                                // allocation of CRB bought from seller remaining
                                checkCRBs += allMEC.get(i).frmSeller;
                                allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet += allMEC.get(i).frmSeller;
                                allMEC.get(i).frmSeller = 0;
                                allESP.get(allMEC.get(i).ServESP.get(j).ID).q -= allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet;
                                System.out.println("From Buyer MEC " + i + " own ESP " + allMEC.get(i).ServESP.get(j).ID + " fraction from seller CRB got = " + allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet);
                                //// $$$$$ buyer utility for ESP
                                allMEC.get(i).utilMEC += allESP.get(allMEC.get(i).ServESP.get(j).ID).qGet * allESP.get(allMEC.get(i).ServESP.get(j).ID).r[i];

                                allESP.get(allMEC.get(i).ServESP.get(j).ID).mecID = allMEC.get(i).ID;
                            }
                        }
                    }
                }
            }
        }
        System.out.println("Here is the checking result = " + checkCRBs + " if it is equal to available total CRBs then you are error free.");
    }

    void espUtilCal() {
        for (int i = 0; i < allESP.size(); i++) {
            allESP.get(i).calcUtil();
        }
    }

    void printUtilVal() throws IOException {
        double avgESPutil = 0;
        int cnt = 0;
        for (int i = 0; i < allESP.size(); i++) {

            if (allESP.get(i).qGet == 0) {
                allESP.get(i).noF = true;
                System.out.println("utitity of ESP " + i + " = 0 as no CRB available");
                continue;
            }
            System.out.println("utitity of ESP " + i + " = " + allESP.get(i).totUtil + " CRB = " + allESP.get(i).qGet + " req q = " + allESP.get(i).q);
            avgESPutil += allESP.get(i).totUtil;
            cnt++;
        }
        System.out.println("Avg of all ESP utility = " + (avgESPutil / NoESP) + " of sum = " + avgESPutil);
        /*for (int i = 0; i < SystemSE.size(); i++) {
            System.out.println("Seller id = " + SystemSE.get(i) + " total utility = " + (allMEC.get(SystemSE.get(i)).utilMEC + allMEC.get(SystemSE.get(i)).utilSel));
        }*/
        int misESP = 0;

        for (int i = 0; i < NoESP; i++) {
            if ((allESP.get(i).qGet - allESP.get(i).qA) != 0) {
                misESP++;
                //System.out.println("ESP id = " + i + " missed full services");
            }
        }
        double ratio = ((double) NoESP - (double) misESP) / (double) NoESP;
        System.out.println("Ratio of Served ESPs = " + ratio + " served count = " + (NoESP - misESP));

        double totMECutil = 0;
        double mecBUutil = 0;
        double mecSEutil = 0;
        for (int i = 0; i < allMEC.size(); i++) {
            if (allMEC.get(i).b_s) {
                mecSEutil += allMEC.get(i).utilSel;
                totMECutil += allMEC.get(i).utilMEC + allMEC.get(i).utilSel;
                System.out.println("Seller id = " + i + " total utility = " + (allMEC.get(i).utilMEC + allMEC.get(i).utilSel) + " " + allMEC.get(i).initCRB);
            } else {
                mecBUutil += allMEC.get(i).utilMEC;
                totMECutil += allMEC.get(i).utilMEC;
                System.out.println("Buyer id = " + i + " total utility = " + allMEC.get(i).utilMEC + " " + allMEC.get(i).initCRB);
            }
        }
        int bN = 1;
        int sN = 1;
        if (!SystemBU.isEmpty()) {
            bN = SystemBU.size();
        }
        if (!SystemSE.isEmpty()) {
            sN = SystemSE.size();
        }
        System.out.println("Sum of all buyer MEC utility = " + mecBUutil + " avggg = " + (mecBUutil / SystemBU.size()));
        System.out.println("Sum of all seller MEC utility = " + mecSEutil + " avggg = " + (mecSEutil / SystemSE.size()));
        System.out.println("Sum of all MEC utility = " + totMECutil + " avg = " + (totMECutil / NoMEC));
        double exe = (double) acpu / ac * 1000;
        double wait = (double) wt / ac * 1000;
        double dis = 0;
        for (int i = 0; i < allMEC.size(); i++) {
            for (int j = 0; j < allMEC.get(i).MD.size(); j++) {
                dis += DisMEC[i][allMEC.get(i).MD.get(j)];
            }
        }
        dis /= allMEC.size();
        dis = dis / 50;
        System.out.println("avg exe time = " + exe + "ms avg wt = " + wait + "ms cnt " + ac + " dis del = " + dis);
        double TAT = exe + wait + dis * 2 + 2.0/50.0;
        System.out.println("TAT = " + TAT);
        DecimalFormat df = new DecimalFormat("0.00");
        DecimalFormat df2 = new DecimalFormat("0.0000");
        FileWriter w = new FileWriter(F_name, true);
        String string = "Iteration# " + itr + "\r\n";// + "; ld = "+lambda+", mu = "+mu+"\r\n";
        string += "MEC avg = " + df.format(totMECutil / allMEC.size()) + " ESP avg = " + df.format(avgESPutil / NoESP) + " Ratio = " + df2.format(ratio) + " TAT = " + TAT + "\r\n";
        w.write(string);
        w.flush();
        w.close();
    }

    void print() {
        for (int i = 0; i < NoESP; i++) {
            System.out.println("For ESP " + i + " Price " + Arrays.toString(allESP.get(i).r) + " distance " + Arrays.toString(allESP.get(i).dis));
        }
        System.out.println("Info of MECs");

        for (int i = 0; i < NoMEC; i++) // MEC-MEC delay
        {
            System.out.println("Distance of MEC " + i + " " + Arrays.toString(DisMEC[i]));
        }

        for (int i = 0; i < NoMEC; i++) {
            int MECcntESP = 0;
            System.out.print("MEC " + i + " con ESPs");
            for (int j = 0; j < NoESP; j++) {
                if (conESParr[j] == i) {
                    System.out.print(" " + j);
                    MECcntESP++;
                }
            }
            System.out.println(" total " + MECcntESP);
        }
    }

    void MECSt(int mecID) {
        /**
         * The cloudlet list.
         */
        List<Cloudlet> cloudletList = new ArrayList<Cloudlet>();;

        /**
         * The vmlist.
         */
        List<Vm> vmlist = new ArrayList<Vm>();;
        Log.printLine("Starting CloudSimExample2...");

        try {
            // First step: Initialize the CloudSim package. It should be called
            // before creating any entities.
            int num_user = 1;   // number of cloud users
            Calendar calendar = Calendar.getInstance();
            boolean trace_flag = false;  // mean trace events

            // Initialize the CloudSim library
            CloudSim.init(num_user, calendar, trace_flag);

            // Second step: Create Datacenters
            //Datacenters are the resource providers in CloudSim. We need at list one of them to run a CloudSim simulation
            @SuppressWarnings("unused")
            Datacenter datacenter0 = createDatacenter("Datacenter_0", mecID);

            //Third step: Create Broker
            DatacenterBroker broker = createBroker();
            int brokerId = broker.getId();

            //Fourth step: Create one virtual machine
            crVm(brokerId, vmlist, mecID);
            //submit vm list to the broker
            broker.submitVmList(vmlist);

            //Fifth step: Create two Cloudlets
            crClet(brokerId, cloudletList, mecID);
            //submit cloudlet list to the broker
            broker.submitCloudletList(cloudletList);

            //bind the cloudlets to the vms. This way, the broker
            // will submit the bound cloudlets only to the specific VM
            // Sixth step: Starts the simulation
            CloudSim.startSimulation();

            // Final step: Print results when simulation is over
            List<Cloudlet> newList = broker.getCloudletReceivedList();

            CloudSim.stopSimulation();

            printCloudletList(newList, mecID);
        } catch (Exception e) {
            e.printStackTrace();
            Log.printLine("The simulation has been terminated due to an unexpected error");
        }
    }

    void crVm(int brokerId, List vmlist, int mecID) {

        //VM description
        int vmid = 0;
        int mips = 1000;
        long size = 100; //image size (MB)
        int ram = 128; //vm memory (MB)
        long bw = 10;
        int pesNumber = 1; //number of cpus
        String vmm = "Xen"; //VMM name

        //create two VMs
        for (vmid = 0; vmid < allMEC.get(mecID).initCRB; vmid++) {
            Vm vm1 = new Vm(vmid, brokerId, mips, pesNumber, ram, bw, size, vmm, new CloudletSchedulerSpaceShared());

            //add the VMs to the vmList
            vmlist.add(vm1);
        }
    }

    void crClet(int brokerId, List cloudletList, int mecID) {

        //Cloudlet properties
        //int id = 0;
        int pesNumber = 1;
        long length = 10;
        long fileSize = 5;
        long outputSize = 5;
        UtilizationModel utilizationModel = new UtilizationModelFull();
        for (int id = 0; id < allMEC.get(mecID).tR; id++) {
            Cloudlet cloudlet1 = new Cloudlet(id, length, pesNumber, fileSize, outputSize, utilizationModel, utilizationModel, utilizationModel);
            cloudlet1.setUserId(brokerId);

            //add the cloudlets to the list
            cloudletList.add(cloudlet1);
        }

    }

    private Datacenter createDatacenter(String name, int mecID) {

        // Here are the steps needed to create a PowerDatacenter:
        // 1. We need to create a list to store
        //    our machine
        List<Host> hostList = new ArrayList<Host>();

        // 2. A Machine contains one or more PEs or CPUs/Cores.
        // In this example, it will have only one core.
        List<Pe> peList = new ArrayList<Pe>();

        int mips = 1000 * 10;

        // 3. Create PEs and add these into a list.
        for (int i = 0; i < 40; i++) {
            peList.add(new Pe(i, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
        }//        peList.add(new Pe(1, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(2, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(3, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(4, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(5, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(6, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(7, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(8, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(9, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(10, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(11, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(12, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(13, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(14, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(15, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(16, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(17, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(18, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating
//        peList.add(new Pe(19, new PeProvisionerSimple(mips))); // need to store Pe id and MIPS Rating

        //4. Create Host with its id and list of PEs and add them to the list of machines
        int hostId = 0;
        int ram = 2048 * 100; //host memory (MB)
        long storage = 1000000; //host storage
        int bw = 10000;

        hostList.add(
                new Host(
                        hostId,
                        new RamProvisionerSimple(ram),
                        new BwProvisionerSimple(bw),
                        storage,
                        peList,
                        new VmSchedulerTimeShared(peList)
                )
        ); // This is our machine

        // 5. Create a DatacenterCharacteristics object that stores the
        //    properties of a data center: architecture, OS, list of
        //    Machines, allocation policy: time- or space-shared, time zone
        //    and its price (G$/Pe time unit).
        String arch = "x86";      // system architecture
        String os = "Linux";          // operating system
        String vmm = "Xen";
        double time_zone = 10.0;         // time zone this resource located
        double cost = 3.0;              // the cost of using processing in this resource
        double costPerMem = 0.05;		// the cost of using memory in this resource
        double costPerStorage = 0.001;	// the cost of using storage in this resource
        double costPerBw = 0.0;			// the cost of using bw in this resource
        allMEC.get(mecID).cccc = (costPerMem + costPerStorage) * 1;
        LinkedList<Storage> storageList = new LinkedList<Storage>();	//we are not adding SAN devices by now

        DatacenterCharacteristics characteristics = new DatacenterCharacteristics(
                arch, os, vmm, hostList, time_zone, cost, costPerMem, costPerStorage, costPerBw);

        // 6. Finally, we need to create a PowerDatacenter object.
        Datacenter datacenter = null;
        try {
            datacenter = new Datacenter(name, characteristics, new VmAllocationPolicySimple(hostList), storageList, 0);
        } catch (Exception e) {
            e.printStackTrace();
        }

        return datacenter;
    }

    //We strongly encourage users to develop their own broker policies, to submit vms and cloudlets according
    //to the specific rules of the simulated scenario
    private DatacenterBroker createBroker() {

        DatacenterBroker broker = null;
        try {
            broker = new DatacenterBroker("Broker");
        } catch (Exception e) {
            e.printStackTrace();
            return null;
        }
        return broker;
    }

    /**
     * Prints the Cloudlet objects
     *
     * @param list list of Cloudlets
     */
    private void printCloudletList(List<Cloudlet> list, int mecID) {
        int size = list.size();
        Cloudlet cloudlet;

        double dd = 0;
        String indent = "    ";
        Log.printLine();
        Log.printLine("========== OUTPUT ==========");
        Log.printLine("Cloudlet ID" + indent + "STATUS" + indent
                + "Data center ID" + indent + "VM ID" + indent + "Time" + indent + "Start Time" + indent + "Finish Time");

        DecimalFormat dft = new DecimalFormat("###.##");
        for (int i = 0; i < size; i++) {
            cloudlet = list.get(i);
            Log.print(indent + cloudlet.getCloudletId() + indent + indent);

            if (cloudlet.getCloudletStatus() == Cloudlet.SUCCESS) {
                Log.print("SUCCESS");
                acpu += cloudlet.getActualCPUTime();
                wt += cloudlet.getWaitingTime();
                ac++;
                dd += cloudlet.getFinishTime();
                Log.printLine(indent + indent + cloudlet.getResourceId() + indent + indent + indent + cloudlet.getVmId()
                        + indent + indent + dft.format(cloudlet.getActualCPUTime()) + indent + indent + dft.format(cloudlet.getExecStartTime())
                        + indent + indent + dft.format(cloudlet.getFinishTime()));
            }
        }
        allMEC.get(mecID).dddd = (dd / (double) size);
        System.out.println("avgggggggggggggggggggggggggggg= " + allMEC.get(mecID).dddd);

    }
}

public class FinalSim {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) throws IOException {
        // TODO code application logic here
        for (int i = 1; i <= 15; i++) {
            St s = new St(i);
            //St s = new St(1);
        }
    }
}
