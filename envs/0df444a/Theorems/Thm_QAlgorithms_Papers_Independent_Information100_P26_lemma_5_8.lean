-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_lemma_5_8
-- name    : QAlgorithms.Papers.Independent.Information100.P26.lemma_5_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:41:53.503616+00:00
-- url     : https://prove2.me/theorems/371ddc57-3c41-4915-850f-4997b03fa286
-- title:
--   Lemma 5.8: the two block-size cases for a zero-extended channel
-- statement:
--   For the positive coordinate block algebra $A=\bigoplus_l\mathbb C I_{m_l}$, fix a block $k$ and a unital channel $\phi$ on $M_{m_k}$. Let $\iota_k$ denote zero extension. Then normalized independent Haar integration over $U(A')$ gives
--   $$\int\!\int\operatorname{Re}\langle\beta_{U,V},\iota_k\phi\rangle\beta_{U,V}\,dU\,dV=\begin{cases}E_A+\dfrac{\iota_k\phi-\iota_k\delta_{m_k}}{(m_k-1)(m_k+1)^2},&m_k>1,\\E_A,&m_k=1.\end{cases}$$
--   Both block-size regimes are included. The singular denominator is never evaluated in the singleton branch.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 19, Lemma 5.8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Lemma 5.8, PDF pp.19. -/
theorem lemma_5_8 {d : ℕ} (hd : 0 < d) (b : Blocks d)
    (mu : Measure (Unitary d)) (hmu : CommutantHaar (blockAlgebra b) mu)
    (k : Fin b.count) (t : Map (b.size k)) (ht : UnitalChannel t) :
    weightedIntegral mu (fun U V => (hsInner (beta U V) (includeBlock b k t)).re) =
      if 1 < b.size k then expectation (blockAlgebra b) +
        (integralDenominator (b.size k))⁻¹ •
          (includeBlock b k t - includeBlock b k (depolarizing (b.size k)))
      else expectation (blockAlgebra b) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
