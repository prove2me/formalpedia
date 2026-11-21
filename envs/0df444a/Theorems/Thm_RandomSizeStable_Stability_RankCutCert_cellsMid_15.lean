-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_15
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_15
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:36.400961+00:00
-- url     : https://prove2.me/theorems/16497d78-2366-46ed-a12d-0b9d031ec1ce
-- title:
--   Rank-cut certificate at D* — certified p-cells on [3133/4096, 809/1024]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [3133/4096, 809/1024]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [3133/4096, 809/1024] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_15 :
    CellOK (3133 / 4096 : ℝ) (1577 / 2048 : ℝ) (4331536913 / 804128209 : ℝ) (-2164688918 / 688077227 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (-248299508217 / 997508999603 : ℝ), (-54032685 / 260187958 : ℝ), (-180395529425 / 977868784162 : ℝ), (-158689782683 / 973713270544 : ℝ), (-7718267575 / 54491586619 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (84120793 / 258490608 : ℝ), (58158258 / 214211351 : ℝ), (116426735 / 482734099 : ℝ), (131186654 / 615704355 : ℝ), (94091184 / 508111475 : ℝ), (0 : ℝ), (0 : ℝ)] ∧
    CellOK (1577 / 2048 : ℝ) (1587 / 2048 : ℝ) (4351030479 / 823577617 : ℝ) (-1983806479 / 658808067 : ℝ) (0 : ℝ)
      ![(-38676 / 97620574055 : ℝ), (16200 / 781039543001 : ℝ), (1304 / 62869030057 : ℝ), (-62050 / 490522186303 : ℝ), (-108315 / 963997332013 : ℝ), (19426 / 936538022987 : ℝ), (1304 / 62869030057 : ℝ), (-63527 / 842924339084 : ℝ), (-260466902410 / 841099938693 : ℝ)]
      ![(119 / 231227191 : ℝ), (-20 / 750816617 : ℝ), (-10 / 375409317 : ℝ), (123 / 748135970 : ℝ), (32 / 219105157 : ℝ), (-22 / 825867747 : ℝ), (-10 / 375409317 : ℝ), (85 / 867311373 : ℝ), (379493259 / 943628095 : ℝ)] ∧
    CellOK (1587 / 2048 : ℝ) (3195 / 4096 : ℝ) (1623632853 / 295115656 : ℝ) (-811686836 / 246398529 : ℝ) (0 : ℝ)
      ![(-1144845335 / 974210674 : ℝ), (-639275556217 / 998260204080 : ℝ), (-218545436928 / 485672620421 : ℝ), (-314843938319 / 838661863292 : ℝ), (-294740760016 / 883803924471 : ℝ), (-126157559 / 428209517 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(1513051723 / 997715717 : ℝ), (590126954 / 714081999 : ℝ), (139451867 / 240144799 : ℝ), (217318919 / 448576036 : ℝ), (336239381 / 781288224 : ℝ), (80156567 / 210828404 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)] ∧
    CellOK (3195 / 4096 : ℝ) (3215 / 4096 : ℝ) (4409168966 / 792132007 : ℝ) (-2732551082 / 809332383 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (-183310442 / 197366815 : ℝ), (0 : ℝ), (-67275553 / 123560627 : ℝ), (-434165126 / 897639451 : ℝ), (-285641936 / 668492093 : ℝ), (0 : ℝ), (0 : ℝ), (-882359645 / 843601264 : ℝ)]
      ![(0 : ℝ), (1015373549 / 852753849 : ℝ), (0 : ℝ), (539484003 / 772880434 : ℝ), (246363787 / 397314835 : ℝ), (545922547 / 996589375 : ℝ), (0 : ℝ), (0 : ℝ), (1210435663 / 902701595 : ℝ)] ∧
    CellOK (3215 / 4096 : ℝ) (809 / 1024 : ℝ) (4722477671 / 887823973 : ℝ) (-734998211 / 240141496 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)] := by
  sorry
