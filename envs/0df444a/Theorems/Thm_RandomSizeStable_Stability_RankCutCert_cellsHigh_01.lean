-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsHigh_01
-- name    : RandomSizeStable.Stability.RankCutCert.cellsHigh_01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:12:56.117905+00:00
-- url     : https://prove2.me/theorems/24673cfb-b022-4e67-a082-b9360515c813
-- title:
--   Rank-cut certificate at D* — certified p-cells on [3891/4096, 1019/1024]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients ($l_2 = 0$): for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [3891/4096, 1019/1024]$, near $p = 1$ (the bracket checked as $B/(1-p)$). The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [3891/4096, 1019/1024] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsHigh_01 :
    CellOK (3891 / 4096 : ℝ) (3973 / 4096 : ℝ) (-10851251392 / 877719851 : ℝ) (3301243388 / 224377671 : ℝ) (0 : ℝ)
      ![(24042370306791 / 992387262611 : ℝ), (20928111161 / 909305781 : ℝ), (19036257127 / 996943430 : ℝ), (15711659484 / 994319045 : ℝ), (584515121 / 44051169 : ℝ), (6634613507 / 564852980 : ℝ), (17199236747 / 982399654 : ℝ), (3764554030 / 302501869 : ℝ), (2573394780 / 201588017 : ℝ)]
      ![(-2144859044 / 85873917 : ℝ), (-20145787124 / 849120013 : ℝ), (-13500932658 / 688891489 : ℝ), (-15415857806 / 955645539 : ℝ), (-4691328420 / 348395899 : ℝ), (-11763587057 / 992811031 : ℝ), (-3158945896 / 178114749 : ℝ), (-6948276102 / 559340843 : ℝ), (-12467024043 / 990280106 : ℝ)] ∧
    CellOK (3973 / 4096 : ℝ) (4035 / 4096 : ℝ) (13533573913 / 854997614 : ℝ) (-11881242294 / 840263893 : ℝ) (0 : ℝ)
      ![(1079369 / 844445338430 : ℝ), (-1330268154 / 764056921 : ℝ), (-3144618933 / 524507237 : ℝ), (-7263740060040 / 657115138177 : ℝ), (-7421129788781 / 512591330295 : ℝ), (-11012732980435 / 634720739854 : ℝ), (-686071211 / 35698655 : ℝ), (-17117828260 / 878469219 : ℝ), (-17340532121 / 926062215 : ℝ)]
      ![(-687 / 529512124 : ℝ), (1659233895 / 924384586 : ℝ), (2964144313 / 479531838 : ℝ), (11013285137 / 966399460 : ℝ), (6228229424 / 417277001 : ℝ), (9026268936 / 504608389 : ℝ), (660685307 / 33303310 : ℝ), (9663355142 / 478280893 : ℝ), (3464364141 / 176868479 : ℝ)] ∧
    CellOK (4035 / 4096 : ℝ) (1019 / 1024 : ℝ) (-47712665693 / 388327988 : ℝ) (31061151326 / 247757923 : ℝ) (0 : ℝ)
      ![(60407082808 / 472550179 : ℝ), (114485078181 / 907986634 : ℝ), (50823809645 / 402587729 : ℝ), (51641803379 / 408196765 : ℝ), (121979152426 / 963788933 : ℝ), (46324611482 / 365602829 : ℝ), (18934904167 / 149313816 : ℝ), (125477793874 / 987221129 : ℝ), (107012076761 / 837905508 : ℝ)]
      ![(-74932067537 / 583313479 : ℝ), (-61985250367 / 489409467 : ℝ), (-100919143817 / 796244904 : ℝ), (-86909609080 / 684631701 : ℝ), (-48068773835 / 378672497 : ℝ), (-46065974060 / 362606129 : ℝ), (-104093698483 / 819066036 : ℝ), (-121870832072 / 957419781 : ℝ), (-70497553173 / 551826017 : ℝ)] := by
  sorry
