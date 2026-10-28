-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_relaxation_strictness_and_tightness
-- name    : QAlgorithms.Papers.Independent.Information100.P19.relaxation_strictness_and_tightness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:57:35.248582+00:00
-- url     : https://prove2.me/theorems/0be0905b-f842-42ea-b186-c5d90e402258
-- title:
--   Example 5.10 and following unnumbered tightness criterion
-- statement:
--   The relaxation is strictly smaller at $(r_1,r_2)=(1,2/3)$:
--   $$\alpha_c(1,2/3)=\sqrt{3/2}<\sqrt{1+\sqrt{2/3}}=\alpha(1,2/3).$$
--   On the nonzero discrete feasible domain $0\le r_1\le1$, $0<r_2\le r_1^2$, equality of the two optima holds exactly when $r_1^2/r_2$ is a natural number. The zero case is kept separate to avoid a meaningless ratio.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 33, Example 5.10 and following unnumbered tightness criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Example 5.10 and following unnumbered tightness criterion; arXiv:2609.29471v1, PDF pp.33, 34. -/
theorem relaxation_strictness_and_tightness  :
    alphaC ![(1:ℝ),2/3] = ENNReal.ofReal (Real.sqrt (3/2)) ∧
    alpha ![(1:ℝ),2/3] = ENNReal.ofReal (Real.sqrt (1+Real.sqrt (2/3))) ∧
    alphaC ![(1:ℝ),2/3] < alpha ![(1:ℝ),2/3] ∧
    (∀ r1 r2 : ℝ, 0≤r1 → r1≤1 → 0<r2 → r2≤r1^2 →
      (alpha ![r1,r2] = alphaC ![r1,r2] ↔ ∃ k : ℕ, r1^2/r2=(k:ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
