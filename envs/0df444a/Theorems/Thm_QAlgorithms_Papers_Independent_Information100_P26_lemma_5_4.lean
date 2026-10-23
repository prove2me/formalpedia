-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_lemma_5_4
-- name    : QAlgorithms.Papers.Independent.Information100.P26.lemma_5_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:36:15.83422+00:00
-- url     : https://prove2.me/theorems/f83f538d-d3ee-4e88-b4a3-0080518b6ad6
-- title:
--   Lemma 5.4: central block invariance and reduction
-- statement:
--   Let $\tau$ be a unital quantum channel on $M_d$, $d\ge1$, and let the unital $C^*$-subalgebra $A$ be fixed pointwise by $\tau$. Let $P_1,\ldots,P_r$ be its complete family of minimal nonzero central projections. Then
--   $$\tau(P_kM_dP_l)\subseteq P_kM_dP_l\quad\text{for every }k,l.$$
--   Moreover $Z(A)'$ and its Hilbert–Schmidt orthogonal complement are invariant under $\tau$. Thus $Z(A)'$ reduces $\tau$; $A$ need not be commutative.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 18, Lemma 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Lemma 5.4, PDF pp.18. -/
theorem lemma_5_4 {d r : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (A : Submodule ℂ (Mat d)) (hA : CStar A) (hfix : Fixes t A)
    (P : Fin r → Mat d) (hP : MinimalCentralFamily A P) :
    (∀ k l : Fin r, ∀ X : Mat d,
      ∃ Y : Mat d, applyMap t (P k * X * P l) = P k * Y * P l) ∧
    Reduces t (commutant (center (A : Set (Mat d)))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
