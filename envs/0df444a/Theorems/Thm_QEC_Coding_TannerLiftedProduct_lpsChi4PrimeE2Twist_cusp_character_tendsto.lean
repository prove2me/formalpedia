-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeE2Twist_cusp_character_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_cusp_character_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:54:40.379208+00:00
-- url     : https://prove2.me/theorems/f48c1c26-847e-4f7b-a672-0a62f73a54ed
-- title:
--   Tanner Lifted Product: lps Chi4 Prime E2 Twist cusp character tendsto
-- statement:
--   The full signed cusp limit of the iterated twist is the product of the two actual single-character constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L523-L574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L523-L574

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_cusp_character_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4PrimeE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (lpsChi4EisensteinCuspConstant γ*lpsQuadraticEisensteinCuspConstant q γ)) := by sorry
