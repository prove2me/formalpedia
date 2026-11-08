-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicE4PowerAtLevel_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicE4PowerAtLevel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:21:09.616976+00:00
-- url     : https://prove2.me/theorems/d2d8aff4-45e0-4056-bf26-251cc97260b7
-- title:
--   Tanner Lifted Product: lps Original Meromorphic E4 Power At Level apply
-- statement:
--   The restricted denominator retains the literal E4 cube-power values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L52-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L52-L55

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicE4PowerAtLevel_apply (N k : ℕ) (τ : ℍ) :
    lpsOriginalMeromorphicE4PowerAtLevel N k τ =
      (ModularForm.E₄ τ^3)^k := by sorry
