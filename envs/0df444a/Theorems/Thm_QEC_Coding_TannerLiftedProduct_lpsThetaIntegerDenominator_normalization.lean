-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaIntegerDenominator_normalization
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaIntegerDenominator_normalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:40:58.199196+00:00
-- url     : https://prove2.me/theorems/1253ddf9-9b11-4891-8f9e-b0b78715abad
-- title:
--   Tanner Lifted Product: lps Theta Integer Denominator normalization
-- statement:
--   Actual common normalization is cleared, including two-adic halves and prime denominators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L21-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L21-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaIntegerDenominator_normalization (q : ℕ) [Fact q.Prime] :
    (lpsThetaIntegerDenominator q : ℂ)*lpsThetaEisensteinNormalization q = 2*(q : ℂ) := by sorry
