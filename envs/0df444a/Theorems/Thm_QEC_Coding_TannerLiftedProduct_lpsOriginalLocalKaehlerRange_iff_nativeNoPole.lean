-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLocalKaehlerRange_iff_nativeNoPole
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLocalKaehlerRange_iff_nativeNoPole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:22:59.093237+00:00
-- url     : https://prove2.me/theorems/57c9b865-c5d2-4ce5-8067-3c85d6a9bee1
-- title:
--   Tanner Lifted Product: lps Original Local Kaehler Range iff native No Pole
-- statement:
--   The real original Ω(V/C) image is exactly the no-pole actual native covector condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeLocalDifferentialComparison.lean#L247-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeLocalDifferentialComparison.lean#L247-L254

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "Cov" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_26
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_28
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_142
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_148
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_149
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_150
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_151
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_152
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_156
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_158
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_160
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_162
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_163
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_164
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_221
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_222
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_223
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_224
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_228
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_230
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_232
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_234

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLocalKaehlerRange_iff_nativeNoPole
    (differentialForm : KaehlerDifferential ℂ K) :
    differentialForm ∈ ((KaehlerDifferential.D ℂ K).compAlgebraMap V).liftKaehlerDifferential.range ↔
      0 ≤ meromorphicOrderValuation a
        (lpsOriginalNativeCovectorToLocal N hN x
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm)) := by sorry
