-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4EisensteinCuspConstant_dilation
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4EisensteinCuspConstant_dilation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:06:46.682839+00:00
-- url     : https://prove2.me/theorems/a6214b21-b22d-4a32-b27d-e99c319046c0
-- title:
--   Tanner Lifted Product: lps Chi4 Eisenstein Cusp Constant dilation
-- statement:
--   A modulus-four unit dilation multiplies the reduced cusp constant by its actual character value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L203-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L203-L246

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4EisensteinCuspConstant_dilation (m : ℕ) (hm : 0<m)
    (hm4 : m.Coprime 4) (γ : SL(2,ℤ)) :
    lpsChi4EisensteinCuspConstant (lpsEisensteinDilationCuspMatrix m hm γ)=
      lpsChi4E2Character (m:ZMod 4)*lpsChi4EisensteinCuspConstant γ := by sorry
