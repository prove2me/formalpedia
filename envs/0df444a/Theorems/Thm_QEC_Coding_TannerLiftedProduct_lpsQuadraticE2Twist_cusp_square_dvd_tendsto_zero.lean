-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_square_dvd_tendsto_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_square_dvd_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:32.753114+00:00
-- url     : https://prove2.me/theorems/048e547b-14c8-411d-8f41-847c487fa8a3
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist cusp square dvd tendsto zero
-- statement:
--   A denominator divisible by the prime squared makes the actual twist cusp limit vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L348-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L348-L360

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_square_dvd_tendsto_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) (hD : (D:ZMod q)=0) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 0) := by sorry
