-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_cusp_character_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_cusp_character_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:06:20.611486+00:00
-- url     : https://prove2.me/theorems/cb687d25-13cb-4ec4-8b29-a7e5b33fc85a
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Dilate cusp character tendsto
-- statement:
--   At every signed integer cusp the actual quadratic dilation has the gcd-scaled character limit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L103-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L103-L116

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_cusp_character_tendsto (q m : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hm : 0<m) (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        lpsQuadraticEisensteinCuspConstant q (lpsEisensteinDilationCuspMatrix m hm γ))) := by sorry
