-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_level_scalar
-- name    : QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_level_scalar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:49:52.757401+00:00
-- url     : https://prove2.me/theorems/9ae88d4b-60ce-4cc0-bdae-3e7aa1687d12
-- title:
--   Tanner Lifted Product: lps Standard Theta slash level scalar
-- statement:
--   The two actual scale reductions yield the original LPS product times its Gauss scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaGaussScalar.lean#L28-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaGaussScalar.lean#L28-L74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_level_scalar (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      (-(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat *
        lpsUnaryQuadraticGauss (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat^3) *
      lpsStandardTheta q z := by sorry
