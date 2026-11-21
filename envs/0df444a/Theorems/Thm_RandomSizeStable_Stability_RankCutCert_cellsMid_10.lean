-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_10
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_10
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:13.907905+00:00
-- url     : https://prove2.me/theorems/51231ff3-a778-483d-9184-f9cfcc261388
-- title:
--   Rank-cut certificate at D* — certified p-cells on [763/1024, 6119/8192]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [763/1024, 6119/8192]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [763/1024, 6119/8192] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_10 :
    CellOK (763 / 1024 : ℝ) (3057 / 4096 : ℝ) (1026428690 / 588876417 : ℝ) (-116112903 / 118475840 : ℝ) (479894649 / 719712193 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)] ∧
    CellOK (3057 / 4096 : ℝ) (6119 / 8192 : ℝ) (1026428690 / 588876417 : ℝ) (-116112903 / 118475840 : ℝ) (479894649 / 719712193 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)] := by
  sorry
