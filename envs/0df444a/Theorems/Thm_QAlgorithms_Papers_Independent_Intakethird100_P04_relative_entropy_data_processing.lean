-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P04_relative_entropy_data_processing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P04.relative_entropy_data_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:54:35.071577+00:00
-- url     : https://prove2.me/theorems/bf9bc1cb-ce6f-4dce-98e6-6fb4a42f42c0
-- title:
--   Data processing of extended quantum relative entropy
-- statement:
--   Let $\rho,\sigma$ be positive trace-class operators of trace one on an arbitrary complex Hilbert space $H$, and let $\mathcal E$ be a trace-preserving completely positive linear map on trace-class operators, with arbitrary output Hilbert space. Let $D(\rho\Vert\sigma)$ denote Umegaki relative entropy in natural logarithm units, taking the value $+\infty$ on support failure and allowing infinite relative entropy. Then
--
--   $$
--   D(\rho\Vert\sigma)\ge D(\mathcal E(\rho)\Vert\mathcal E(\sigma)).
--   $$
--
--   This expresses the loss of statistical distinguishability under physical processing. The author explicitly draws this known corollary from the overlap inequality; differentiability and entropy finiteness are not additional hypotheses.
--
--   **Formalization Note** The accepted extended relative entropy uses finite orthogonal compressions with the generalized trace correction; on normalized states it is Umegaki relative entropy in nats.
-- source:
--   The Converse Part of The Theorem for Quantum Hoeffding Bound, arXiv:quant-ph/0611289v1, PDF p. 7, Remark 2, (33)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P04

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State operatorTrace relativeEntropy)

open QAlgorithms.Papers.Independent.Support50.P20
  (Effect traceAcceptance IsHilbertCPTP BlockHilbert blockBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator)

variable {H K : Type*}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Remark 2, PDF p.7, (33): extended Umegaki entropy data processing in nats,
including support failure and infinite entropy. Differentiability is not a premise.
The accepted finite-compression trace correction vanishes on normalized states. -/
theorem relative_entropy_data_processing {I J : Type*}
    (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (rho sigma : State b)
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K)) (hPhi : IsHilbertCPTP b d Phi) :
    relativeEntropy
        ⟨Phi rho.val.val, (hPhi.2.2.1 rho.val.val rho.val.property).1⟩
        ⟨Phi sigma.val.val, (hPhi.2.2.1 sigma.val.val sigma.val.property).1⟩ ≤
      relativeEntropy rho.val sigma.val := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P04

end
