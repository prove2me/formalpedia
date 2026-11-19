-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2ThetaBasis_cusp_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2ThetaBasis_cusp_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:35.561491+00:00
-- url     : https://prove2.me/theorems/ee325416-6143-4aac-b992-d9a76988dfe2
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Theta Basis cusp tendsto
-- statement:
--   Every actual common-level quadratic basis form has its proved character-scaled cusp constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L162-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L162-L168

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2ThetaBasis_cusp_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : Fin 5) (γ : SL(2,ℤ)) :
    Tendsto ((lpsQuadraticE2ThetaBasis q hq2 a : ℍ→ℂ) ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        (lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)*lpsQuadraticEisensteinCuspConstant q γ))) := by sorry
