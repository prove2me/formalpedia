-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_adaptive_inversion
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.adaptive_inversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:14:12.557929+00:00
-- url     : https://prove2.me/theorems/3dd379bc-62fb-45c7-9871-5149282979bd
-- title:
--   Adaptive inverse with floor((k+1)/d) attempts
-- statement:
--   For every integer $d\ge2$ and $k\ge0$, a fixed sequential $k$-slot instrument implements the inverse channel of every unknown $U\in U(d)$ exactly on its heralded success branch, with coefficient
--
--   $$p=1-(1-d^{-2})^{\lfloor(k+1)/d\rfloor}.$$
--
--   Memory and auxiliary channels are independent of $U$, and the failure branch is retained. Each full failed attempt and recovery costs $d$ uses, while the last attempt costs $d-1$; unused slots can be padded.
--
--   This is the construction credited by the source to Ref. [29], with no optimality assertion.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 19, VII B

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.18–20, VII B: the adaptive construction credited to Ref. [29].
The displayed exponent is floor((k+1)/d). The preceding sentence incorrectly
calls 1-1/d^2 the success probability; Fig. 8 labels it as failure. -/
theorem adaptive_inversion {d k : ℕ} (hd : 2 ≤ d) :
    Attainable .adaptive d k (targetChoi .inverse)
      (adaptiveInverseProbability d k) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
