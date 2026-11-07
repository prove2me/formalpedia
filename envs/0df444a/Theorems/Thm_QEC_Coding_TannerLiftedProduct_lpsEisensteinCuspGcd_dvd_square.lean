-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_dvd_square
-- name    : QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_dvd_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:26.239112+00:00
-- url     : https://prove2.me/theorems/53460699-98c1-4158-83ed-f870df921a7b
-- title:
--   Tanner Lifted Product: lps Eisenstein Cusp Gcd dvd square
-- statement:
--   The determinant-one identity bounds the actual undilated cusp gcd by the modulus squared.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L22-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L22-L35

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_dvd_square (N : ℤ) (γ : SL(2,ℤ)) (r : ℤ) :
    Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0) ∣ N.natAbs^2 := by sorry
