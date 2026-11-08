-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4Ratio_reciprocal_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4Ratio_reciprocal_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:29:34.519205+00:00
-- url     : https://prove2.me/theorems/9b018147-8a8b-46d8-a0d0-5e173a9b540e
-- title:
--   Tanner Lifted Product: lps Original E4 Ratio reciprocal integral
-- statement:
--   A literal SAME-field E4 ratio is integral by the constructed reciprocal monic equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalFieldIntegral.lean#L70-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalFieldIntegral.lean#L70-L83

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary004

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4Ratio_reciprocal_integral
    (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (f : K)
    (hratio : (lpsOriginalGeneratedFunctionField N hpos).val f =
      (algebraMap R H (lpsOriginalLevelFormHolomorphic N k A)) /
        (algebraMap R H (lpsOriginalE4PowerHolomorphic k))) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f := by sorry
