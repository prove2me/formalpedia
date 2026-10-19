-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_proposition_6_8
-- name    : QAlgorithms.Papers.Independent.Information100.P26.proposition_6_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:45:06.077989+00:00
-- url     : https://prove2.me/theorems/8f4b3b4c-be3b-44a1-a2f4-84523eb42906
-- title:
--   Proposition 6.8: range commutes with the peripheral space
-- statement:
--   Every unital 2-copositive channel $\tau$ on $M_d$, $d\ge1$, satisfies
--   $$\operatorname{Range}(\tau)\subseteq\mathcal P(\tau)'.$$
--   The peripheral space is the span of the modulus-one eigenspaces. This is a conclusion about the original channel, without an eventual assumption or an iterate.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 23, Proposition 6.8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Proposition 6.8, PDF pp.23,24. -/
theorem proposition_6_8 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (hcop : TwoCopositive t) :
    ∀ X : Mat d, applyMap t X ∈ commutant (peripheral t : Set (Mat d)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
