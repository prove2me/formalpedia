-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4PowerHolomorphic_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4PowerHolomorphic_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:21:23.071976+00:00
-- url     : https://prove2.me/theorems/8f67321e-24b2-4bea-8348-1ecdc2622597
-- title:
--   Tanner Lifted Product: lps Original E4 Power Holomorphic apply
-- statement:
--   The bundled holomorphic denominator has the same actual E4 cube-power values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L236-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L236-L238

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4PowerHolomorphic_apply (k : ℕ) (τ : ℍ) :
    (lpsOriginalE4PowerHolomorphic k).val τ = (ModularForm.E₄ τ^3)^k := by sorry
