-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_lemma_5_7
-- name    : QAlgorithms.Papers.Independent.Information100.P26.lemma_5_7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:41:00.440251+00:00
-- url     : https://prove2.me/theorems/bde3b9e2-d1d1-4c25-b649-db4473e3ce18
-- title:
--   Lemma 5.7: weighted Haar average over coordinate block commutants
-- statement:
--   Let $A=\bigoplus_{k=1}^r\mathbb C I_{m_k}$ be a positive consecutive coordinate block algebra and let $\tau$ be a unital channel with $A\subseteq\operatorname{Fix}(\tau)\cap\operatorname{Range}(\tau)'$. Write $\tau_k$ for its actual $k$th diagonal restriction and $\iota_k$ for zero extension. With independent normalized Haar integration over $U(A')$,
--   $$\int\!\int\operatorname{Re}\langle\beta_{U,V},\tau\rangle\beta_{U,V}\,dU\,dV=\tau+(r-1)E_A+\sum_{m_k>1}\left(1-\frac1{(m_k-1)(m_k+1)^2}\right)(\iota_k\delta_{m_k}-\iota_k\tau_k).$$
--   Singleton blocks contribute no denominator term. For one block this recovers the weighted average of Lemma 4.5.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 18, Lemma 5.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Lemma 5.7, PDF pp.18,19. -/
theorem lemma_5_7 {d : ℕ} (hd : 0 < d) (b : Blocks d)
    (mu : Measure (Unitary d)) (hmu : CommutantHaar (blockAlgebra b) mu)
    (t : Map d) (ht : UnitalChannel t) (hcompat : Compatible (blockAlgebra b) t) :
    weightedIntegral mu (fun U V => (hsInner (beta U V) t).re) =
      t + ((b.count : ℝ)-1) • expectation (blockAlgebra b) +
        ∑ k : Fin b.count, if 1 < b.size k then
          (1 - (integralDenominator (b.size k))⁻¹) •
            (includeBlock b k (depolarizing (b.size k)) - includeBlock b k (restrictBlock b k t))
          else 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
