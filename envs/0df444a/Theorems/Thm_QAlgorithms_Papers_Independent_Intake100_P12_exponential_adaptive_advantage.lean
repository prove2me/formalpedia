-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_exponential_adaptive_advantage
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.exponential_adaptive_advantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:58:29.636666+00:00
-- url     : https://prove2.me/theorems/635d390b-8fab-40d5-8fec-9717cf51853b
-- title:
--   Exponential adaptive advantage: quantitative success curves
-- statement:
--   Fix an integer dimension $d\ge2$. For every integer query budget $k\ge1$, there are fixed sequential circuits that implement the transpose and inverse channels of every unknown $U\in U(d)$ exactly on their heralded success branches. Their success probabilities are respectively
--
--   $$p_T^{\rm ad}=1-(1-d^{-2})^{\lceil k/d\rceil},\qquad p_I^{\rm ad}=1-(1-d^{-2})^{\lfloor(k+1)/d\rfloor}.$$
--
--   Every parallel circuit for the respective tasks has constant success probability bounded by
--
--   $$p_T^{\rm par}\le1-\frac{d^2-1}{k+d^2-1},\qquad p_I^{\rm par}\le1-\frac{d^2-1}{k(d-1)+d^2-1}.$$
--
--   These explicit curves express exponential decay of adaptive failure versus the inverse-polynomial parallel lower bounds on failure, at fixed $d$. They do not assert adaptive optimality.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 1, Abstract; Sections VI E and VII A–B

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.1,12,17–20: the abstract's exponential advantage, pinned to the
explicit exponentially decaying adaptive failure probabilities and rational
parallel failure bounds. No optimality of the adaptive constructions is claimed. -/
theorem exponential_adaptive_advantage :
    ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ, 1 ≤ k →
      Attainable .adaptive d k (targetChoi .transpose) (adaptiveTransposeProbability d k) ∧
      (∀ p, Attainable .parallel d k (targetChoi .transpose) p →
        p ≤ parallelTransposeProbability d k) ∧
      Attainable .adaptive d k (targetChoi .inverse) (adaptiveInverseProbability d k) ∧
      (∀ p, Attainable .parallel d k (targetChoi .inverse) p →
        p ≤ parallelTransposeProbability d (k*(d-1))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
