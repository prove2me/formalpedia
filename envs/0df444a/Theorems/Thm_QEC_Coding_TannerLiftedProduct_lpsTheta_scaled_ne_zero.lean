-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_scaled_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsTheta_scaled_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:47:14.823056+00:00
-- url     : https://prove2.me/theorems/977d58c8-0838-419d-b329-c5c1a53325f3
-- title:
--   Tanner Lifted Product: lps Theta scaled ne zero
-- statement:
--   The concrete arithmetic theta lattice vector is genuine and nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L132-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L132-L137

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsTheta_scaled_ne_zero (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4 ≠ 0 := by sorry
