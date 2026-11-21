-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cells_near_one
-- name    : RandomSizeStable.Stability.RankCutCert.cells_near_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:41:42.662998+00:00
-- url     : https://prove2.me/theorems/de078fc6-be7f-43c5-8bc9-b0a44cecbfe1
-- title:
--   Rank-cut certificate at D* — certified p-cells covering $[4095/4096, 1)$
-- statement:
--   There are finitely many $p$-cells $[p_0(k), p_1(k)]$ with real multiplier coefficients $l_0, l_1, l_2, t_0, t_1$ such that `CellOK` (bundle `RandomSizeStable_Stability_RankCutCert`) holds for each cell and every $p$ in $[4095/4096, 1)$ lies in one of them. With the cells of the statements `cellsLow_*`, `cellsMid_*`, `cellsHigh_*` and the $p = 1$ statement `p1_ok`, this completes a rank-cut certificate at $D^\star$. Near $p = 1$ the margin is limited by the cutoffs $h_j$ of the bundle ($\eta_j(\phi(h_j) - \mu) - h_j \approx 3.5\cdot10^{-6}$); a single cell on this range has been certified by an exact integer replica of the bundle's checker with 18,770 leaf boxes, which still has to be split into kernel-sized pieces.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [4095/4096, 1) (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cells_near_one :
    ∃ (n : ℕ) (p0 p1 l0 l1 l2 : Fin n → ℝ) (t0 t1 : Fin n → Fin 9 → ℝ),
      (∀ k, CellOK (p0 k) (p1 k) (l0 k) (l1 k) (l2 k) (t0 k) (t1 k)) ∧
      ∀ p : ℝ, 4095 / 4096 ≤ p → p < 1 → ∃ k, p0 k ≤ p ∧ p ≤ p1 k := by
  sorry
