-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_lemma_5_6
-- name    : QAlgorithms.Papers.Independent.Information100.P26.lemma_5_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:39:47.836988+00:00
-- url     : https://prove2.me/theorems/dfeb6678-79b2-4cb0-92a9-a96d85668156
-- title:
--   Lemma 5.6: coordinate direct sums exactly characterize compatibility
-- statement:
--   Let $A=\bigoplus_{k=1}^r\mathbb C I_{m_k}\subseteq M_d$ be the consecutive coordinate block algebra with all sizes positive and total $d\ge1$. For any unital quantum channel $\tau$,
--   $$\tau=\bigoplus_k\tau_k\text{ for unital channels }\tau_k:M_{m_k}\to M_{m_k}\quad\Longleftrightarrow\quad A\subseteq\operatorname{Fix}(\tau)\cap\operatorname{Range}(\tau)'.$$
--   The direct sum acts on the diagonal input blocks and annihilates all cross blocks, as in Definition 5.5.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 18, Lemma 5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Lemma 5.6, PDF pp.18. -/
theorem lemma_5_6 {d : ℕ} (hd : 0 < d) (b : Blocks d) (t : Map d) (ht : UnitalChannel t) :
    (∃ s : (k : Fin b.count) → Map (b.size k),
      (∀ k, UnitalChannel (s k)) ∧ t = blockSum b s) ↔ Compatible (blockAlgebra b) t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
