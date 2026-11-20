-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaIntegerDenominator_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaIntegerDenominator_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:42:09.423607+00:00
-- url     : https://prove2.me/theorems/cd56a1db-fa71-483f-a07e-2807a605e97d
-- title:
--   Tanner Lifted Product: lps Theta Integer Denominator ne zero
-- statement:
--   The proved denominator is nonzero at every actual residue prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L124-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L124-L129

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaIntegerDenominator_ne_zero (q : ℕ) [Fact q.Prime] :
    lpsThetaIntegerDenominator q≠0 := by sorry
