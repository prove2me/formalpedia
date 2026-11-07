-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRealShiftInverse_tendsto_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsRealShiftInverse_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:12.856208+00:00
-- url     : https://prove2.me/theorems/680b6b7c-8289-484f-9c35-3761586820aa
-- title:
--   Tanner Lifted Product: lps Real Shift Inverse tendsto zero
-- statement:
--   The unchanged imaginary part proves the inverse shifted denominator tends to zero in the full filter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L26-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L26-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsRealShiftInverse_tendsto_zero (r : ℝ) :
    Tendsto (fun z : ℍ => ((z:ℂ)+(r:ℂ))⁻¹) UpperHalfPlane.atImInfty (𝓝 0) := by sorry
