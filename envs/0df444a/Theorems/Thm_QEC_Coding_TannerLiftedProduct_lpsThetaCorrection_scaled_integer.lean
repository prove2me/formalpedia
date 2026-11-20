-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCorrection_scaled_integer
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCorrection_scaled_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:41:10.16005+00:00
-- url     : https://prove2.me/theorems/bd42f3db-0c2c-4ac1-8494-dc805600be2f
-- title:
--   Tanner Lifted Product: lps Theta Correction scaled integer
-- statement:
--   Every actual full correction coefficient has the same cleared integer denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L35-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L35-L108

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCorrection_scaled_integer (q : ℕ) [Fact q.Prime] (n : ℕ) :
    ∃ z : ℤ, (lpsThetaIntegerDenominator q : ℂ)*lpsThetaEisensteinCorrectionCoefficient q n = (z : ℂ) := by sorry
