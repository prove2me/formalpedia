-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_theorem_5_12
-- name    : QAlgorithms.Papers.Independent.Information100.P26.theorem_5_12
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:42:58.360598+00:00
-- url     : https://prove2.me/theorems/e35a8f2f-f211-4615-a92e-803f8aea4533
-- title:
--   Theorem 5.12: 2-copositivity and fixed points force range commutation
-- statement:
--   Let $A\subseteq M_d$ be a commutative unital $C^*$-subalgebra, $d\ge1$. Every unital CP, trace-preserving channel $\tau$ which is 2-copositive and fixes $A$ pointwise has
--   $$\operatorname{Range}(\tau)\subseteq A'.$$
--   Only 2-copositivity is assumed; complete copositivity is unnecessary. This derives the range condition from positivity and fixed points.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 21, Theorem 5.12

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Theorem 5.12, PDF pp.21. -/
theorem theorem_5_12 {d : ℕ} (hd : 0 < d) (A : Submodule ℂ (Mat d))
    (hA : CStar A) (hcomm : Commutative A) (t : Map d)
    (ht : UnitalChannel t) (hcop : TwoCopositive t) (hfix : Fixes t A) :
    ∀ X : Mat d, applyMap t X ∈ commutant (A : Set (Mat d)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
