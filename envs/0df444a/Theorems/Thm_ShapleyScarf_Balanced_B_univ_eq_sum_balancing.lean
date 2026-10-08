-- Prove2me | Theorems.Thm_ShapleyScarf_Balanced_B_univ_eq_sum_balancing
-- name    : ShapleyScarf.Balanced.B_univ_eq_sum_balancing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:30.73347+00:00
-- url     : https://prove2.me/theorems/bcb7d3a0-1d88-413a-9dfd-78fb6a7764ff
-- title:
--   Section 4 — the grand-coalition acceptability matrix identity
-- statement:
--   Let $T$ be a balanced family of coalitions, let $x$ be feasible for every coalition in $T$, and let $\delta_S$ be balancing weights. The acceptability matrix for all traders is the weighted sum of the coalition matrices:
--   $$
--   B_N(x)=\sum_{S\in T}\delta_S B_S(x).
--   $$
--
--   The identity is a matrix equality and holds for every payoff vector $x$ under the balancing equations; feasibility is retained because the paper states this equation in that setting. It lets the family of coalition constraints be compared with a single grand-coalition matrix.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974), DOI 10.1016/0304-4068(74)90033-0; p. 110 of the source printing, Section 4, proof of the Theorem, B_N(x) equation

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem B_univ_eq_sum_balancing {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) (T : Finset (Finset N)) (x : N → ℝ)
    (δ : Finset N → ℝ)
    (hT : IsBalancedFamily T)
    (hx : ∀ S ∈ T, x ∈ marketGame A S)
    (hδ : IsBalancingWeights T δ) :
    acceptableMatrix A Finset.univ x =
      ∑ S ∈ T, δ S • acceptableMatrix A S x := by sorry

end ShapleyScarf.Balanced
