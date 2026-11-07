-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_gcd_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_gcd_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:59.5582+00:00
-- url     : https://prove2.me/theorems/b8f09be5-7e8f-4bee-a359-1c8f68d45065
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist cusp gcd tendsto
-- statement:
--   The dilation-one specialization computes every actual cusp constant of the existing twist.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L286-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L286-L293

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_gcd_tendsto (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((q:ℤ)*γ 1 0):ℕ):ℂ)^2/(q:ℂ)^2))) := by sorry
