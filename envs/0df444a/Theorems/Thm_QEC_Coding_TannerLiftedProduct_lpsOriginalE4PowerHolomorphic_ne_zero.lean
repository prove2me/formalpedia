-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4PowerHolomorphic_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4PowerHolomorphic_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:22:24.962179+00:00
-- url     : https://prove2.me/theorems/d35d3bcc-164c-48d4-82f4-587e960f3e6d
-- title:
--   Tanner Lifted Product: lps Original E4 Power Holomorphic ne zero
-- statement:
--   The genuine qconstant1 proves that the E4 denominator is nonzero as a holomorphic function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L241-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L241-L250

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4PowerHolomorphic_ne_zero (k : ℕ) :
    lpsOriginalE4PowerHolomorphic k ≠ 0 := by sorry
