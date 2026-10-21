-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition8
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:51:35.317418+00:00
-- url     : https://prove2.me/theorems/d3f7bc3b-2bcb-48a1-97ba-e45585abd586
-- title:
--   Proposition 8: one faithful pure-state test
-- statement:
--   Let $H,H',K$ be separable complex Hilbert spaces, $k\ge1$, and $\Phi:\mathcal T(H)\to\mathcal T(H')$ a channel. Suppose a normalized pure state $\psi$ on $H\otimes K$ has faithful reduced states on both factors, and
--
--   $$(\Phi\otimes\operatorname{Id}_K)(|\psi\rangle\langle\psi|)\in S_k.$$
--
--   Then $\Phi$ is $k$-partially entanglement breaking. Faithfulness means a zero kernel, not a positive uniform lower spectral bound. The reduced states act on different spaces.
--
--   One faithful purification therefore suffices to test the condition that otherwise quantifies over all ancillas and inputs.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 10, Proposition 8: one faithful pure-state test

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF pp.10–11, Proposition 8. Both reduced states are
faithful (zero kernel), not boundedly invertible or equal on different spaces. -/
theorem proposition8 {I J A : Type} [Countable I] [Countable J] [Countable A]
    (k : ℕ) (hk : 0 < k) (Phi : CanonicalChannel I J) (psi : PureState (I × A))
    (hleft : faithful (traceSecond psi.val.coefficients))
    (hright : faithful (traceFirst psi.val.coefficients))
    (hout : classArray k (tensorApply (canonicalChannelAction Phi) psi.val.coefficients)) : isPEB k Phi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
