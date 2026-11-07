-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_not_dvd_tendsto_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_not_dvd_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:43.843681+00:00
-- url     : https://prove2.me/theorems/b7766c1f-2610-4e13-9f06-3cd8880f21f9
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist cusp not dvd tendsto zero
-- statement:
--   The full cusp limit vanishes when the residue prime does not divide the denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L257-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L257-L274

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_not_dvd_tendsto_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (hC : ¬(q:ℤ)∣γ 1 0) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 0) := by sorry
