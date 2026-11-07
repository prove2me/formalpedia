-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspGcd
-- name    : QEC.Coding.TannerLiftedProduct.lpsEisensteinDilationCuspGcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:42.755911+00:00
-- url     : https://prove2.me/theorems/059bd9d4-5350-4e0f-b147-13a1f3d4c0c1
-- title:
--   Tanner Lifted Product: lps Eisenstein Dilation Cusp Gcd
-- statement:
--   The actual affine cusp gcd scales by the true dilation-denominator gcd.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L54-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L54-L67

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsEisensteinDilationCuspGcd (N r : ℤ) (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    Int.gcd (N*(m:ℤ)*γ 0 0+r*γ 1 0) (N*γ 1 0)=
      Int.gcd (m:ℤ) (γ 1 0)*
        Int.gcd (N*lpsEisensteinDilationCuspMatrix m hm γ 0 0+
          r*lpsEisensteinDilationCuspMatrix m hm γ 1 0)
          (N*lpsEisensteinDilationCuspMatrix m hm γ 1 0) := by sorry
