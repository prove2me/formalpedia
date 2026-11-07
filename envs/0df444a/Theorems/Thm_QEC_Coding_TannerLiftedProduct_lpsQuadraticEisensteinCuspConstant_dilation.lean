-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspConstant_dilation
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspConstant_dilation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:07:14.364481+00:00
-- url     : https://prove2.me/theorems/01afef4c-50b3-4879-bd40-1178e55bbaa4
-- title:
--   Tanner Lifted Product: lps Quadratic Eisenstein Cusp Constant dilation
-- statement:
--   A prime-unit dilation multiplies the reduced quadratic cusp constant by its actual character value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L138-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L138-L194

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspConstant_dilation (q m : ℕ) [Fact q.Prime]
    (hm : 0<m) (hmq : m.Coprime q) (γ : SL(2,ℤ)) :
    lpsQuadraticEisensteinCuspConstant q (lpsEisensteinDilationCuspMatrix m hm γ)=
      lpsQuadraticE2Character q (m:ZMod q)*lpsQuadraticEisensteinCuspConstant q γ := by sorry
