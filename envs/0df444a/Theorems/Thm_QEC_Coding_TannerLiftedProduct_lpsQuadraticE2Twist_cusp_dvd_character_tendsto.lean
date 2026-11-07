-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_dvd_character_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_dvd_character_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:24.257188+00:00
-- url     : https://prove2.me/theorems/97217ee1-0b1f-4b0e-9019-e7fdc67e42aa
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist cusp dvd character tendsto
-- statement:
--   When the denominator has exactly one prime factor its full cusp limit is the actual root character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L318-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L318-L336

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_dvd_character_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) (hD : (D:ZMod q)≠0) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-(γ 0 0:ZMod q)/(D:ZMod q)))) := by sorry
