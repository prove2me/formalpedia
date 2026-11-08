-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalPolynomial_field_embedding
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalPolynomial_field_embedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:30:55.495204+00:00
-- url     : https://prove2.me/theorems/31f1328b-0a1f-4028-b2e0-c1d8bf7aeac5
-- title:
--   Tanner Lifted Product: lps Original Reciprocal Polynomial field embedding
-- statement:
--   The existing reciprocal polynomial map commutes with inclusion into the actual holomorphic fraction field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalFieldIntegral.lean#L35-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalFieldIntegral.lean#L35-L67

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
omit [NeZero N]

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalPolynomial_field_embedding :
    (lpsOriginalGeneratedFunctionField N hpos).val.toRingHom.comp
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos) =
    Polynomial.eval₂RingHom ((algebraMap R H).comp (algebraMap ℂ R))
      (algebraMap R H lpsOriginalJHolomorphic)⁻¹ := by sorry
