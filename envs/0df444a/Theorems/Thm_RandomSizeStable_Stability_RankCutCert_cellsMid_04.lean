-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_04
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_04
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:24.290026+00:00
-- url     : https://prove2.me/theorems/bc0ff526-74e2-4601-a46d-c1375c209f8f
-- title:
--   Rank-cut certificate at D* — certified p-cells on [2355/4096, 1331/2048]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [2355/4096, 1331/2048]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [2355/4096, 1331/2048] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_04 :
    CellOK (2355 / 4096 : ℝ) (1229 / 2048 : ℝ) (1473086539 / 310281090 : ℝ) (-216176121 / 96165947 : ℝ) (0 : ℝ)
      ![(1226612545 / 378322147 : ℝ), (5079078949 / 885447755 : ℝ), (2610184117 / 919974680 : ℝ), (1124810726 / 435862593 : ℝ), (869586728 / 715068739 : ℝ), (1707537941 / 453524028 : ℝ), (-726629 / 558950 : ℝ), (1671750487 / 937827893 : ℝ), (1190713925 / 716755899 : ℝ)]
      ![(-3630810007 / 795452432 : ℝ), (-2898630773 / 325949221 : ℝ), (-3433754597 / 808960951 : ℝ), (-2070525789 / 515696309 : ℝ), (-1570939757 / 871917285 : ℝ), (-5702260640 / 942635293 : ℝ), (1793340001 / 734581058 : ℝ), (-220146343 / 80396995 : ℝ), (-907657204 / 356849397 : ℝ)] ∧
    CellOK (1229 / 2048 : ℝ) (5 / 8 : ℝ) (3429867323 / 739411553 : ℝ) (-384853601 / 185050614 : ℝ) (0 : ℝ)
      ![(10591095989 / 848410070 : ℝ), (254568377 / 85332495 : ℝ), (3063673349 / 759014395 : ℝ), (177713045 / 98135333 : ℝ), (2580226721 / 958051529 : ℝ), (353906387 / 148746485 : ℝ), (1762141549 / 852170708 : ℝ), (1561205407 / 880518663 : ℝ), (596038332 / 389819447 : ℝ)]
      ![(-13845755329 / 715036157 : ℝ), (-962261252 / 222640775 : ℝ), (-4827521379 / 781744360 : ℝ), (-2645027512 / 961830185 : ℝ), (-898219391 / 220104179 : ℝ), (-2357700127 / 653975894 : ℝ), (-1999629209 / 638190220 : ℝ), (-304725426 / 113304361 : ℝ), (-393339445 / 171093318 : ℝ)] ∧
    CellOK (5 / 8 : ℝ) (1331 / 2048 : ℝ) (4866262792 / 987961283 : ℝ) (-2118535025 / 837197664 : ℝ) (0 : ℝ)
      ![(1627910431 / 840680577 : ℝ), (2913031657 / 996483506 : ℝ), (866963122 / 319088605 : ℝ), (-917486934 / 890626739 : ℝ), (-1029583539 / 461831500 : ℝ), (-228035015 / 115784603 : ℝ), (-480744928 / 280861029 : ℝ), (-833771375 / 605391037 : ℝ), (949436047 / 993821937 : ℝ)]
      ![(-1589674786 / 636394277 : ℝ), (-1365762159 / 322446365 : ℝ), (-3431334107 / 842293419 : ℝ), (378071223 / 217413044 : ℝ), (2123127818 / 595220827 : ℝ), (1913103772 / 607110603 : ℝ), (2474076227 / 903378739 : ℝ), (2075445699 / 939926272 : ℝ), (-1017949921 / 735405333 : ℝ)] := by
  sorry
