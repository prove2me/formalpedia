-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroMeromorphicValuationRing_isDiscreteValuationRing
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroMeromorphicValuationRing_isDiscreteValuationRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:57:52.555554+00:00
-- url     : https://prove2.me/theorems/484c3352-1231-4740-8f54-bb5153a67512
-- title:
--   Tanner Lifted Product: lps Original Zero Meromorphic Valuation Ring is Discrete Valuation Ring
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Zero Meromorphic Valuation Ring is Discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationLocalRings.lean#L142-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationLocalRings.lean#L142-L152

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_22
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_27
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_28
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_29
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_30
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_59
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_112
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_113

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroMeromorphicValuationRing_isDiscreteValuationRing
    (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    IsDiscreteValuationRing
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by sorry
