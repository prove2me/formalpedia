-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_example_6_18
-- name    : QAlgorithms.Papers.Independent.Information100.P26.example_6_18
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:00:12.689984+00:00
-- url     : https://prove2.me/theorems/7ad0d231-3b1c-48a4-80a4-b825bebf619d
-- title:
--   Example 6.18: primitive eventually MTD channels without 2-copositivity
-- statement:
--   Let $d\ge2$ and $1/(d+1)<\lambda<1$. For $\tau_\lambda=\lambda\operatorname{id}+(1-\lambda)\delta_d$,
--   $$\tau_\lambda\text{ is a unital primitive channel, is eventually MTD, and is not 2-copositive}.$$
--   This strengthens the earlier eventual-EB example by identifying both primitivity and eventual MTD.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 26, Example 6.18

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Example 6.18, PDF pp.26. -/
theorem example_6_18 {d : ℕ} (hd : 2 ≤ d) (a : ℝ)
    (ha : 1 / ((d : ℝ)+1) < a) (ha1 : a < 1) :
    UnitalChannel (depolarizingMixture d a) ∧ Primitive (depolarizingMixture d a) ∧
      Eventually MTD (depolarizingMixture d a) ∧ ¬ TwoCopositive (depolarizingMixture d a) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
