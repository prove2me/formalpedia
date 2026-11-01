-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P04_petz_data_processing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P04.petz_data_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:53:45.146548+00:00
-- url     : https://prove2.me/theorems/48910dba-ca6d-4adf-b8ce-0ea05b958813
-- title:
--   Data processing of Petz overlaps and their log moments
-- statement:
--   Let $\rho,\sigma$ be arbitrary density operators on a complex Hilbert space $H$, and let $\mathcal E$ be a trace-preserving completely positive linear map on trace-class operators, with arbitrary output Hilbert space. For $0\le s\le1$ define
--
--   $$
--   m_s(\rho,\sigma)=\operatorname{Tr}(\rho^{1-s}\sigma^s),\qquad
--   \varphi(s\mid\rho\Vert\sigma)=\log m_s(\rho,\sigma).
--   $$
--
--   Powers of exponent zero are the identity. The fractional-power product is trace class; its trace is nonnegative, and the logarithm is extended with $\log0=-\infty$. For every $s\in[0,1]$,
--
--   $$
--   m_s(\rho,\sigma)\le m_s(\mathcal E(\rho),\mathcal E(\sigma)),\qquad
--   \varphi(s\mid\rho\Vert\sigma)\le\varphi(s\mid\mathcal E(\rho)\Vert\mathcal E(\sigma)).
--   $$
--
--   At either endpoint the overlaps equal one. The paper credits Uhlmann and Petz for earlier proofs and presents these inequalities as a consequence of its operational approach; their statements do not require its conversion formula as a hypothesis.
-- source:
--   The Converse Part of The Theorem for Quantum Hoeffding Bound, arXiv:quant-ph/0611289v1, PDF p. 7, Remark 2, (31)–(32)

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

/-- Remark 2, PDF p.7, (31)--(32): both overlap and extended log-moment
inequalities on [0,1]. Ordinary A^0=I makes endpoints equalities, also for singular
states. Source credits Uhlmann [14] and Petz [15], claiming a new proof. -/
theorem petz_data_processing {I J : Type*}
    (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (rho sigma : State b)
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K)) (hPhi : IsHilbertCPTP b d Phi)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ENNReal.ofReal (traceAcceptance b
        (CFC.rpow rho.val.val (1 - s)) (CFC.rpow sigma.val.val s)) ≤
        ENNReal.ofReal (traceAcceptance d
          (CFC.rpow (Phi rho.val.val) (1 - s)) (CFC.rpow (Phi sigma.val.val) s)) ∧
      logMoment b rho.val.val sigma.val.val s ≤
        logMoment d (Phi rho.val.val) (Phi sigma.val.val) s := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P04

end
