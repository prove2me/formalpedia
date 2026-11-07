-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeE2Twist_cusp_gcd_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_cusp_gcd_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:17:10.361479+00:00
-- url     : https://prove2.me/theorems/529b4c0a-230b-41db-ac03-f9e63e38ffea
-- title:
--   Tanner Lifted Product: lps Chi4 Prime E2 Twist cusp gcd tendsto
-- statement:
--   Dilation one gives the complete actual double-weighted gcd cusp vector of the undilated form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L340-L349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L340-L349

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_cusp_gcd_tendsto (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4PrimeE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
            ∑ a : Fin q,lpsQuadraticE2Character q (a.val:ZMod q)*
              (((Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
                (((4*q:ℕ):ℤ)*γ 1 0):ℕ):ℂ)^2/((4*q:ℕ):ℂ)^2)))) := by sorry
