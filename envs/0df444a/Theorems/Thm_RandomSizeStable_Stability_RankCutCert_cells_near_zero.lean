-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cells_near_zero
-- name    : RandomSizeStable.Stability.RankCutCert.cells_near_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:41:42.122143+00:00
-- url     : https://prove2.me/theorems/26bdb415-b14a-4812-aed7-7d17404635ba
-- title:
--   Rank-cut certificate at D* — certified p-cells covering $(0, 1/512]$
-- statement:
--   There are finitely many $p$-cells $[p_0(k), p_1(k)]$ with real multiplier coefficients $l_0, l_1, l_2, t_0, t_1$ such that `CellOK` (bundle `RandomSizeStable_Stability_RankCutCert`) holds for each cell and every $p$ in $(0, 1/512]$ lies in one of them. With the cells of the statements `cellsLow_*`, `cellsMid_*`, `cellsHigh_*` and the $p = 1$ statement `p1_ok`, this completes a rank-cut certificate at $D^\star$. Near $p = 0$ the slack $G_2$ is $O(p)$; with $a = p(1-w)$ its limit $G_2/p \to -(1-w) + l_0(\mu - w\phi(A)) - t_{0,j}(\mu - \phi(\rho_j(A)))$ for $A \le b$ is positive but only of order $l_0(\mu - \phi(b)) \approx 5\cdot10^{-8}\, l_0$ at $w = 1$, $A = b$, so a certificate needs large $l_0$ and fine subdivision there.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering (0, 1/512] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cells_near_zero :
    ∃ (n : ℕ) (p0 p1 l0 l1 l2 : Fin n → ℝ) (t0 t1 : Fin n → Fin 9 → ℝ),
      (∀ k, CellOK (p0 k) (p1 k) (l0 k) (l1 k) (l2 k) (t0 k) (t1 k)) ∧
      ∀ p : ℝ, 0 < p → p ≤ 1 / 512 → ∃ k, p0 k ≤ p ∧ p ≤ p1 k := by
  sorry
