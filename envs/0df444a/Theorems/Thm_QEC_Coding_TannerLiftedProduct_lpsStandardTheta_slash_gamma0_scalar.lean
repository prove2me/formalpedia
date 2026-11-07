-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_gamma0_scalar
-- name    : QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_gamma0_scalar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T00:20:01.516585+00:00
-- url     : https://prove2.me/theorems/a5a0885b-dce4-4ceb-ad1c-7178fd569008
-- title:
--   Tanner Lifted Product: lps Standard Theta slash gamma0 scalar
-- statement:
--   Exact scalar law for every actual Gamma0 matrix; scalar normalization is not assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaGaussScalar.lean#L95-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaGaussScalar.lean#L95-L114

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_gamma0_scalar (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (16*q^2)) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      lpsThetaGammaGaussScalar q γ * lpsStandardTheta q z := by sorry
