-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_cusp_character_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_cusp_character_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:40.149195+00:00
-- url     : https://prove2.me/theorems/3371a27b-8eba-4756-9e4f-6d631288cac9
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Twist cusp character tendsto
-- statement:
--   The actual modulus-four twist has the full-filter character limit at every integer cusp matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L145-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L145-L180

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_cusp_character_tendsto (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Twist ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (lpsChi4EisensteinCuspConstant γ)) := by sorry
