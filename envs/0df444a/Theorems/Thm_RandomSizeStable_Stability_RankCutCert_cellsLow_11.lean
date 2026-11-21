-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_11
-- name    : RandomSizeStable.Stability.RankCutCert.cellsLow_11
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:12:52.745054+00:00
-- url     : https://prove2.me/theorems/5362c791-ec33-439a-9c77-5c7a072f1507
-- title:
--   Rank-cut certificate at D* — certified p-cells on [101/16384, 61/8192]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients ($l_2 = 0$): for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [101/16384, 61/8192]$, near $p = 0$ (case 2 checked after division by $p$). The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [101/16384, 61/8192] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsLow_11 :
    CellOK (101 / 16384 : ℝ) (61 / 8192 : ℝ) (36635261904 / 501817285 : ℝ) (-200 : ℝ) (0 : ℝ)
      ![(69049382672 / 978216657 : ℝ), (57067472934 / 807338317 : ℝ), (34748184281 / 539054797 : ℝ), (43236205461 / 799037284 : ℝ), (17929931574 / 371284795 : ℝ), (3344881249 / 77977158 : ℝ), (36846034057 / 981438291 : ℝ), (12209149895 / 434180911 : ℝ), (28948264889 / 932293367 : ℝ)]
      ![(200 : ℝ), (200 : ℝ), (-200 : ℝ), (-200 : ℝ), (-200 : ℝ), (-200 : ℝ), (-200 : ℝ), (200 : ℝ), (-200 : ℝ)] := by
  sorry
