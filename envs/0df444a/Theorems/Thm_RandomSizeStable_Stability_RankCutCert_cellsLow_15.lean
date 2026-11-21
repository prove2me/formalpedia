-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_15
-- name    : RandomSizeStable.Stability.RankCutCert.cellsLow_15
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:12:46.517707+00:00
-- url     : https://prove2.me/theorems/432cc4bf-791c-4048-8cfd-15cb41166ab3
-- title:
--   Rank-cut certificate at D* — certified p-cells on [123/8192, 41/2048]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients ($l_2 = 0$): for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [123/8192, 41/2048]$, near $p = 0$ (case 2 checked after division by $p$). The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [123/8192, 41/2048] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsLow_15 :
    CellOK (123 / 8192 : ℝ) (41 / 2048 : ℝ) (21848860955 / 521510688 : ℝ) (-200 : ℝ) (0 : ℝ)
      ![(307826833 / 7957350 : ℝ), (32694488846 / 944487223 : ℝ), (15317563248 / 485439605 : ℝ), (22635917969 / 679760593 : ℝ), (6951152691 / 245956898 : ℝ), (22919410819 / 855445744 : ℝ), (10373007826 / 432471421 : ℝ), (4348665236 / 238757079 : ℝ), (11005608098 / 892764263 : ℝ)]
      ![(102257914325 / 994467016 : ℝ), (200 : ℝ), (141158039077 / 793497087 : ℝ), (-200 : ℝ), (-93884377711 / 840150496 : ℝ), (-178725667868 / 941216561 : ℝ), (-200 : ℝ), (-63732902905 / 997663852 : ℝ), (200 : ℝ)] := by
  sorry
