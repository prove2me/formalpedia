-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_obs14_Tco_le_iff_partial_sums
-- name    : StochFictPlay.Supermodular.obs14_Tco_le_iff_partial_sums
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:18:39.607506+00:00
-- url     : https://prove2.me/theorems/3a484e87-c87e-455f-a118-4cca9d4c780f
-- title:
--   Observation (14) — stochastic dominance through partial sums
-- statement:
--   Let $x, y$ be probability vectors on the ordered set $\{1, \dots, m\}$ and let $T$ be the stochastic dominance coordinates, $(Tx)_i = \sum_{j > i} x_j$. Then
--   $$T y \ge T x \iff \sum_{i=1}^{k} (y_i - x_i) \le 0 \ \text{ for all } k < m.$$
--
--   It restates dominance of $y$ over $x$ as "the cumulative mass of $y$ on low strategies never exceeds that of $x$", which is the form condition (13) of Lemma A.2 needs.
--
--   **Formalization Note** Strategies are 0-based; the first $k$ strategies are those with index below $k$ (for $k = 0$ the sum is empty).
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 28, observation (14)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_StochOrder

namespace StochFictPlay.Supermodular

/-- Observation (14) (Hofbauer–Sandholm 2002, manuscript p. 28). For mixed strategies
`x, y ∈ ∆S` on `m` ordered strategies, `T y ≥ T x` (stochastic dominance of `y` over `x`) if and
only if `∑_{i=1}^{k} (y_i − x_i) ≤ 0` for every `k < m`. Strategies are 0-based, so the partial
sum over the first `k` strategies is the sum over `i.val < k` (the case `k = 0` is the empty sum
and holds trivially). -/
theorem obs14_Tco_le_iff_partial_sums (m : ℕ) (x y : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m)) :
    Tco x ≤ Tco y ↔
      ∀ k : ℕ, k < m → ∑ i : Fin m, (if i.val < k then y i - x i else 0) ≤ 0 := by sorry

end StochFictPlay.Supermodular
