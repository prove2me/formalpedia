-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_cusp_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_cusp_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:17.633197+00:00
-- url     : https://prove2.me/theorems/01eabd59-ec69-464b-8ceb-acbe5611cc43
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Dilate cusp tendsto
-- statement:
--   Actual finite weighted full-filter limits give the entire dilated twist cusp vector as a gcd sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L247-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L247-L273

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_cusp_tendsto (q m : ℕ) [Fact q.Prime] (hm : 0<m)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((Int.gcd ((q:ℤ)*(m:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((q:ℤ)*γ 1 0):ℕ):ℂ)^2/((q:ℂ)^2*(m:ℂ)^2)))) := by sorry
