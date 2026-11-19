-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_two_factor
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_two_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:58.031197+00:00
-- url     : https://prove2.me/theorems/317c6e08-7f05-4ca4-82c3-da9c11dcd29d
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product two factor
-- statement:
--   The actual two-primary Gauss factor equals the full gcd-character cusp factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L207-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L207-L244

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_two_factor (q t L : ℕ) (hq : Odd q) (hL : Odd L)
    (γ : SL(2,ℤ)) (hC : γ 1 0=((2^t*L:ℕ):ℤ))
    (ha : IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod (2 ^ t))) :
    lpsThetaCuspGaussProduct q (γ 0 0*(L:ℤ)) (2^t)=
      (4/3:ℂ)*((2^t:ℕ):ℂ)^2*
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ) := by sorry
