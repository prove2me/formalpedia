-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_example_2_11
-- name    : QAlgorithms.Papers.Independent.Information100.P26.example_2_11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:47:48.456663+00:00
-- url     : https://prove2.me/theorems/ff8369bd-5eb1-4798-9532-64a7bc979420
-- title:
--   Example 2.11: eventually EB without 2-copositivity
-- statement:
--   Let $d\ge2$ and $1/(d+1)<\lambda<1$. The map $\tau_\lambda=\lambda\operatorname{id}+(1-\lambda)\delta_d$ is a unital quantum channel and
--   $$\tau_\lambda\text{ is eventually EB},\qquad\tau_\lambda\text{ is not 2-copositive and is not PPT}.$$
--   This separates single-step positivity properties from their eventual versions.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 7, Example 2.11

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Example 2.11, PDF pp.7. -/
theorem example_2_11 {d : ℕ} (hd : 2 ≤ d) (a : ℝ)
    (ha : 1 / ((d : ℝ)+1) < a) (ha1 : a < 1) :
    UnitalChannel (depolarizingMixture d a) ∧ Eventually EB (depolarizingMixture d a) ∧
      ¬ TwoCopositive (depolarizingMixture d a) ∧ ¬ PPT (depolarizingMixture d a) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
