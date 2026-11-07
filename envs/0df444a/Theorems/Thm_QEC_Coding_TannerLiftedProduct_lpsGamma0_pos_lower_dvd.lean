-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_pos_lower_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0_pos_lower_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:49:57.464713+00:00
-- url     : https://prove2.me/theorems/0c409b80-2e8e-4977-a993-b72d10509299
-- title:
--   Tanner Lifted Product: lps Gamma0 pos lower dvd
-- statement:
--   Actual Mathlib congruence membership implies natural lower-left divisibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaGaussScalar.lean#L88-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaGaussScalar.lean#L88-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0_pos_lower_dvd (N : ℕ) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (hc : 0 < γ 1 0) : N ∣ (γ 1 0).toNat := by sorry
