-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Dilate_cusp_character_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Dilate_cusp_character_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:06:07.816985+00:00
-- url     : https://prove2.me/theorems/b357f6e7-b12b-497f-934f-aaba415577fc
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Dilate cusp character tendsto
-- statement:
--   At every signed integer cusp the actual modulus-four dilation has the gcd-scaled character limit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L86-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L86-L100

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Dilate_cusp_character_tendsto (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        lpsChi4EisensteinCuspConstant (lpsEisensteinDilationCuspMatrix m hm γ))) := by sorry
