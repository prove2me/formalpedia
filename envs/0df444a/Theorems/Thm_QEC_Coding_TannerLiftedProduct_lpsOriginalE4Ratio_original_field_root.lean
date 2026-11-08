-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4Ratio_original_field_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4Ratio_original_field_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:22:17.06403+00:00
-- url     : https://prove2.me/theorems/ae0f45d8-1fde-4536-86c8-f19373cceee5
-- title:
--   Tanner Lifted Product: lps Original E4 Ratio original field root
-- statement:
--   Homogenization proves the original coset equation root for the actual E4 fraction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L264-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L264-L299

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "P" => Polynomial ℂ

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4Ratio_original_field_root
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k)).eval₂
      ((algebraMap R H).comp lpsOriginalJHolomorphicEval.toRingHom)
      ((algebraMap R H (lpsOriginalLevelFormHolomorphic N k A)) /
        (algebraMap R H (lpsOriginalE4PowerHolomorphic k))) = 0 := by sorry
