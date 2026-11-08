-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLocalKaehlerRange_iff_noPole
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLocalKaehlerRange_iff_noPole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:15:52.50232+00:00
-- url     : https://prove2.me/theorems/c7ace98c-ee15-4d2a-a12c-bddf0a3a7be1
-- title:
--   Tanner Lifted Product: lps Original Local Kaehler Range iff no Pole
-- statement:
--   The original real local Kähler image equals analytic no-pole coefficients, with all prerequisites proved.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalRegularDifferentialComparison.lean#L117-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalRegularDifferentialComparison.lean#L117-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_25
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_30
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_31
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_32
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_33
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_34
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_38
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_40
variable (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_47
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_58
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_59
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_61
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_62
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_63
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_64
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_68
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_70
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_72
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_75
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_78
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_113
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_114

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLocalKaehlerRange_iff_noPole (ω : KaehlerDifferential ℂ K) :
    ω ∈ ((KaehlerDifferential.D ℂ K).compAlgebraMap V).liftKaehlerDifferential.range ↔
      0 ≤ meromorphicOrderValuation a (lpsOriginalFieldLocalDifferentialMap N hpos hN x ω) := by sorry
