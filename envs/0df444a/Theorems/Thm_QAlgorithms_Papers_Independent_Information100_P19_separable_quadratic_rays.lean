-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_separable_quadratic_rays
-- name    : QAlgorithms.Papers.Independent.Information100.P19.separable_quadratic_rays
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:50:34.351974+00:00
-- url     : https://prove2.me/theorems/7090622b-0781-4a0b-aa4b-34d06d11d97c
-- title:
--   Corollary 4.10
-- statement:
--   In quotient coefficient order $(t^2,\pi,\pi_A,\pi_B)$, the separable quadratic cone has exactly four extremal generators: $\pi$, $\pi_A-\pi$, $\pi_B-\pi$, and $t^2+\pi-\pi_A-\pi_B$. For coefficients $(c_t,c_\pi,c_A,c_B)$, membership is equivalent to
--   $$c_t\ge0,\quad c_t+c_A\ge0,\quad c_t+c_B\ge0,\quad c_t+c_\pi+c_A+c_B\ge0.$$
--   Every member has a unique nonnegative decomposition in those four generators. The statement concerns the quotient, whose lineality has been removed.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 26, Corollary 4.10

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Corollary 4.10; arXiv:2609.29471v1, PDF pp.26, 27. -/
theorem separable_quadratic_rays  :
    extremeRays quadCone = {R | ∃ j : Fin 4, R = ray (quadGenerators j)} ∧
    (∀ c : Fin 4 → ℝ, c ∈ quadCone ↔
      0 ≤ c 0 ∧ 0 ≤ c 0+c 2 ∧ 0 ≤ c 0+c 3 ∧ 0 ≤ c 0+c 1+c 2+c 3) ∧
    (∀ c ∈ quadCone, ∃! w : Fin 4 → ℝ,
      (∀ j, 0 ≤ w j) ∧ c = ∑ j, w j • quadGenerators j) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
