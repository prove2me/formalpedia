-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_09
-- name    : RandomSizeStable.Stability.RankCutCert.cellsLow_09
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:12:48.945458+00:00
-- url     : https://prove2.me/theorems/466d52e6-70dc-499f-b467-c48236136a85
-- title:
--   Rank-cut certificate at D* — certified p-cells on [17/4096, 5/1024]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients ($l_2 = 0$): for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [17/4096, 5/1024]$, near $p = 0$ (case 2 checked after division by $p$). The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [17/4096, 5/1024] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsLow_09 :
    CellOK (17 / 4096 : ℝ) (5 / 1024 : ℝ) (13623846040 / 96460611 : ℝ) (-200 : ℝ) (0 : ℝ)
      ![(91955108816 / 659652875 : ℝ), (31725818146 / 225647909 : ℝ), (41228375130 / 341374901 : ℝ), (39306836341 / 389489830 : ℝ), (89603934295 / 998277594 : ℝ), (79215075679 / 997553899 : ℝ), (50401812237 / 728951348 : ℝ), (47248837917 / 804243919 : ℝ), (16249343319 / 909368378 : ℝ)]
      ![(200 : ℝ), (200 : ℝ), (-200 : ℝ), (-200 : ℝ), (-200 : ℝ), (-200 : ℝ), (-200 : ℝ), (-200 : ℝ), (-200 : ℝ)] := by
  sorry
