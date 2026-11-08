-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4Ratio_reciprocal_field_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4Ratio_reciprocal_field_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:26:17.844802+00:00
-- url     : https://prove2.me/theorems/550052e6-7a5a-4247-b2c9-a5cec179e7b3
-- title:
--   Tanner Lifted Product: lps Original E4 Ratio reciprocal field root
-- statement:
--   Inner reflection gives the constructed monic reciprocal-j root in the actual holomorphic fraction field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L302-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L302-L327

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4Ratio_reciprocal_field_root
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalReciprocalE4MonicEquation N k A).eval₂
      (Polynomial.eval₂RingHom ((algebraMap R H).comp (algebraMap ℂ R))
        (algebraMap R H lpsOriginalJHolomorphic)⁻¹)
      ((algebraMap R H (lpsOriginalLevelFormHolomorphic N k A)) /
        (algebraMap R H (lpsOriginalE4PowerHolomorphic k))) = 0 := by sorry
