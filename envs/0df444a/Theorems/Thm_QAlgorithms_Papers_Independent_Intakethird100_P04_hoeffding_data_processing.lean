-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P04_hoeffding_data_processing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P04.hoeffding_data_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:53:01.937203+00:00
-- url     : https://prove2.me/theorems/aace082a-7374-4e11-bdaf-31026c5f2737
-- title:
--   Data processing of the operational Hoeffding exponent
-- statement:
--   Let $\rho,\sigma$ be arbitrary density operators on a complex Hilbert space $H$, and let $\mathcal E$ be a trace-preserving completely positive linear map from trace-class operators on $H$ to trace-class operators on a complex Hilbert space $K$. For a pair $\tau,\upsilon$, write $\alpha_n[T_n]=1-\operatorname{Tr}(\tau^{\otimes n}T_n)$ and $\beta_n[T_n]=\operatorname{Tr}(\upsilon^{\otimes n}T_n)$. Define $B(r\mid\tau\Vert\upsilon)$ as the supremum of $-\ell$ over all sequences of bounded effects on the completed tensor powers for which $n^{-1}\log\alpha_n[T_n]$ has an existing extended limit $\ell$ and $\limsup_{n\to\infty}n^{-1}\log\beta_n[T_n]\le-r$. Logarithms are natural and $\log0=-\infty$. For every $r>0$,
--
--   $$
--   B(r\mid\rho\Vert\sigma)\ge B(r\mid\mathcal E(\rho)\Vert\mathcal E(\sigma)).
--   $$
--
--   The statement expresses monotonicity of the operational testing tradeoff under a physical channel, including infinite exponents. It imposes no restriction on $r$ relative to relative entropy.
-- source:
--   The Converse Part of The Theorem for Quantum Hoeffding Bound, arXiv:quant-ph/0611289v1, PDF p. 7, Remark 2, (30)

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

/-- Remark 2, PDF p.7, (30): operational data processing for every r>0.
CPTP is on full trace class, with no dimension or Kraus-rank bound. No restriction
relative to D and no assumption of conversion formula (29) are introduced. -/
theorem hoeffding_data_processing {I J : Type}
    (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (rho sigma : State b)
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K)) (hPhi : IsHilbertCPTP b d Phi)
    (r : ℝ) (hr : 0 < r) :
    hoeffdingB d (Phi rho.val.val) (Phi sigma.val.val) r ≤
      hoeffdingB b rho.val.val sigma.val.val r := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P04

end
