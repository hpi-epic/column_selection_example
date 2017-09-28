reset;

option randseed'';
option solver cplex;

########  Definition of Workload  ##########

param N := 50;							# number of columns
param Q := 10*N; 						# number of queries


param dd :=10;                          # scan costs main memory
param dr := 1;                          # scan costs second storage


param a {i in 1..N} := Uniform(1,100);                            # size of column i

param b {j in 1..Q} := round(Uniform(1,2000));					  # frequency of query j


param Z {j in 1..Q} := round(Uniform(0.5,10));			          # average number of columns used in query j
                  
set q {j in 1..Q} := union {1..Z[j]}  {round(Uniform(1,N^(1/0.2))^0.2)}; # query j
																					
param g {i in 1..N} := sum{j in 1..Q:card({i} inter q[j])=1} b[j];# frequency of column i
param gmax := max{i in 1..N} g[i];                                # maximal frequency

param s {i in 1..N} :=  Uniform(0,0.1)+0.05*(g[i]/gmax)^0.01;     # selectivity column i

param y {i in 1..N} := round(Uniform(0,1));   	        # current/old allocation



param beta default 0;                              		# penalty reallocation


param w default 0.2;                                    # relative budget

param A2 := sum{i in 1..N} a[i];                        # maximal budget


########  Integer Solution via Linear Solver  ##########

param performance_int;
param RAMused_int;

var x {i in 1..N} <=1, >=0, binary;						# column i in DRAM (1 yes) or (0 no)

var z {i in 1..N} <=1, >=0, binary;			            # column i im DRAM (1 yes) or (0 no)

var f {j in 1..Q} = sum{i in q[j]} (dr*x[i]+dd*(1-x[i])) * a[i]*prod{k in q[j]:s[k]<s[i]} s[k];
                                                        # scan costs for query j


minimize zfkt_int: sum{j in 1..Q} b[j]*f[j]  +  beta  * sum{i in 1..N} a[i]*z[i];


subject to nb1a: sum{i in 1..N} a[i]*x[i] <= w*A2;      # budget constraint

subject to nb2a {i in 1..N}: y[i] - x[i] <= z[i];       # linearization reallocation
subject to nb3a {i in 1..N}: x[i] - y[i] <= z[i];


objective zfkt_int; solve; 								# solve integer program

let performance_int := sum{j in 1..Q} b[j]*f[j];
let RAMused_int     :=(sum{i in 1..N} a[i]*x[i])/A2;


display x;                                              # show column selection
display performance_int, RAMused_int;
display N, Q, _solve_elapsed_time;


########  Continuous Solution via Linear Solver  ##########

param performance_cont;
param RAMused_cont;

param alpha  default 100000;  						    # penalty for budget used

var x2{i in 1..N} <=1, >=0;          					# column i in DRAM (1 yes) or (0 no)

var z2{i in 1..N} <=1, >=0;                  			# column i im DRAM (1 yes) or (0 no)


var f2{j in 1..Q} = sum{i in q[j]} (dr*x2[i]+dd*(1-x2[i])) * a[i]*prod{k in q[j]:s[k]<s[i]} s[k];
                                                        # scan costs for query j

minimize zfkt_cont: sum{j in 1..Q} b[j]*f2[j]  +  alpha * sum{i in 1..N} a[i]*x2[i]
                                               +  beta  * sum{i in 1..N} a[i]*z2[i];


#subject to nb0 {i in 1..N:a[i]>w*A2}: x2[i] = 0;

subject to nb2b {i in 1..N}: y[i] - x2[i] <= z2[i];     # linearization reallocation
subject to nb3b {i in 1..N}: x2[i] - y[i] <= z2[i];

drop nb1a; drop nb2a; drop nb3a;
fix x; fix z;

objective zfkt_cont; solve;            					# solve continuous problem

let performance_cont := sum{j in 1..Q} b[j]*f2[j];
let RAMused_cont     :=(sum{i in 1..N} a[i]*x2[i])/A2;


display x2;                                             # show column selection
display performance_cont, RAMused_cont;
display N, Q, _solve_elapsed_time;

#end;


########  Definition of Numerical Allocation Strategies  ##########


#### (H1) most occurences - best g_i

set kmostused {i in 0..N} :=  if i=0 then {} else if i=N then {ii in 1..N:g[ii]>0} else kmostused[i+1] diff
                 {min{k in kmostused[i+1]:
	         g[k]=min{j in kmostused[i+1]} g[j]} k};
			 
param use := if w>0 then max{k in 0..N: sum{j in kmostused[k]} a[j]<= w*A2}	k;
param space {k in 0..N} := (sum{j in kmostused[k]} a[j]) / A2;
set order ordered default {}; for {i in 1..N} let order:=order union kmostused[i];;


######## (H2) best selectivity - best s_i

set kmostused2 {i in 0..N} :=  if i=0 then {} else if i=N then {ii in 1..N:g[ii]>0} else kmostused2[i+1] diff
                 {min{k in kmostused2[i+1]:
	         s[k]=max{j in kmostused2[i+1]} s[j]} k};
			 
param use2 := if w>0 then max{k in 0..N: sum{j in kmostused2[k]} a[j]<= w*A2}	k;
param space2 {k in 0..N} := (sum{j in kmostused2[k]} a[j]) / A2;
set order2 ordered default {}; for {i in 1..N} let order2:=order2 union kmostused2[i];;


######## (H3) best selectivity/occurences ratio - bestes s_i/g_i

set kmostused3 {i in 0..N} :=  if i=0 then {} else if i=N then {ii in 1..N:g[ii]>0} else kmostused3[i+1] diff
                 {min{k in kmostused3[i+1]:
	         if g[k]>0 then s[k]/g[k] else 1 = max{j in kmostused3[i+1]} if g[j]>0 then s[j]/g[j] else 1} k};

param use3 := if w>0 then max{k in 0..N: sum{j in kmostused3[k]} a[j]<= w*A2}	k;
param space3 {k in 0..N} := (sum{j in kmostused3[k]} a[j]) / A2;
set order3 ordered default {}; for {i in 1..N} let order3:=order3 union kmostused3[i];;


######## (H4) explicit solution via performance order  

param S {i in 1..N,j in 1..Q:card(q[j] inter {i})=1} := prod{k in q[j]:s[k]<s[i]} s[k];

param p {i in 1..N} :=  (sum{j in 1..Q} if card(q[j] inter {i})=1 then b[j]*(dr-dd)*S[i,j]) + beta*(1-2*y[i]);

set kmostused4 {i in 0..N} :=  if i=0 then {} else if i=N then {ii in 1..N:g[ii]>0} else kmostused4[i+1] diff
                 {min{k in kmostused4[i+1]:
	         p[k]=max{j in kmostused4[i+1]} p[j]} k};
			 
param use4 := if w>0 then max{k in 0..N: sum{j in kmostused4[k]} a[j]<= w*A2}	k;
param space4 {k in 0..N} := (sum{j in kmostused4[k]} a[j]) / A2;
set order4 ordered default {}; for {i in 1..N} let order4:=order4 union kmostused4[i];;




########   (H1)-(H4) for a fixed single budget w   ######

param performance_heu;
param performance_heu2;
param performance_heu3;
param performance_heu4;

param used_heu;
param used_heu2;
param used_heu3;
param used_heu4;


let w:= 0.2;

for {i in 1..N} let x[i]:=0; for {i in kmostused[use]}   let x[i]:=1;
let performance_heu:= sum{j in 1..Q} b[j]*f[j];
let used_heu:=(sum{i in 1..N} a[i]*x[i])/A2;
display performance_heu, used_heu;

for {i in 1..N} let x[i]:=0; for {i in kmostused2[use2]} let x[i]:=1;
let performance_heu2:= sum{j in 1..Q} b[j]*f[j];
let used_heu2:=(sum{i in 1..N} a[i]*x[i])/A2;
display performance_heu2, used_heu2;

for {i in 1..N} let x[i]:=0; for {i in kmostused3[use3]} let x[i]:=1;
let performance_heu3:= sum{j in 1..Q} b[j]*f[j];
let used_heu3:=(sum{i in 1..N} a[i]*x[i])/A2;
display performance_heu3, used_heu3;

for {i in 1..N} let x[i]:=0; for {i in kmostused4[use4]} let x[i]:=1;
let performance_heu4:= sum{j in 1..Q} b[j]*f[j];
let used_heu4:=(sum{i in 1..N} a[i]*x[i])/A2;
display performance_heu4, used_heu4;


#end;


######   Strategies (H1)-(H4) for multiple budgets w   ######


printf"" > results_out.txt;

for {k in 0..1 by 0.01} {let w:=k;
			   
for {i in 1..N} let x[i]:=0; for {i in kmostused[use]} let x[i]:=1;
for {j in order diff kmostused[use]} {
    if a[j]+sum{i in 1..N} a[i]*x[i]<=w*A2 then let x[j]:=1; };
let performance_heu:= sum{j in 1..Q} b[j]*f[j];
let used_heu:=(sum{i in 1..N} a[i]*x[i])/A2;


for {i in 1..N} let x[i]:=0; for {i in kmostused2[use2]} let x[i]:=1;
for {j in order2 diff kmostused2[use2]} {
    if a[j]+sum{i in 1..N} a[i]*x[i]<=w*A2 then let x[j]:=1; };
let performance_heu2:= sum{j in 1..Q} b[j]*f[j];
let used_heu2:=(sum{i in 1..N} a[i]*x[i])/A2;


for {i in 1..N} let x[i]:=0; for {i in kmostused3[use3]} let x[i]:=1;
for {j in order3 diff kmostused3[use3]} {
    if a[j]+sum{i in 1..N} a[i]*x[i]<=w*A2 then let x[j]:=1; };
let performance_heu3:= sum{j in 1..Q} b[j]*f[j];
let used_heu3:=(sum{i in 1..N} a[i]*x[i])/A2;


for {i in 1..N} let x[i]:=0; for {i in kmostused4[use4]} let x[i]:=1;
for {j in order4 diff kmostused4[use4]} {
    if a[j]+sum{i in 1..N} a[i]*x[i]<=w*A2 then let x[j]:=1; };
let performance_heu4:= sum{j in 1..Q} b[j]*f[j];
let used_heu4:=(sum{i in 1..N} a[i]*x[i])/A2;


printf"%4.4f  %8.2f   %1.6f  %8.2f   %1.6f  %8.2f   %1.6f   %8.2f   %1.6f\n", w,
    performance_heu, used_heu, performance_heu2, used_heu2,
    performance_heu3, used_heu3, performance_heu4, used_heu4 >> results_out.txt;

						};

end;
