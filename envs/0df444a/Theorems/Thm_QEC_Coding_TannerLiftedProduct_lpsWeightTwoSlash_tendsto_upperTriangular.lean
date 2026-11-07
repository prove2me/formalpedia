-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoSlash_tendsto_upperTriangular
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlash_tendsto_upperTriangular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:05.860331+00:00
-- url     : https://prove2.me/theorems/d0694135-9fde-4d9f-a75d-266fb1ba07a8
-- title:
--   Tanner Lifted Product: lps Weight Two Slash tendsto upper Triangular
-- statement:
--   Actual upper-triangular slash action transports the full-filter limit with its scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L84-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L84-L97

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlash_tendsto_upperTriangular (f : ℍ→ℂ) (L : ℂ)
    (hf : Tendsto f UpperHalfPlane.atImInfty (𝓝 L)) (g : GL (Fin 2) ℝ)
    (hc : g 1 0=0) (hd : 0<g.det.val) :
    Tendsto (f ∣[(2:ℤ)] g) UpperHalfPlane.atImInfty
      (𝓝 (L*(g.det.val:ℂ)*(g 1 1:ℂ)^(-(2:ℤ)))) := by sorry
