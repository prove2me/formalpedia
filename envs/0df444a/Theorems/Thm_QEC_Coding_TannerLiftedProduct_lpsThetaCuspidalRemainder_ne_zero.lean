-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspidalRemainder_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainder_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:35:04.935284+00:00
-- url     : https://prove2.me/theorems/cd0841d9-b2ef-45ff-9c8e-67ff89227c54
-- title:
--   Tanner Lifted Product: lps Theta Cuspidal Remainder ne zero
-- statement:
--   The actual theta-minus-complete-correction cusp form is nonzero at every prime level q = 1 mod 4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaPeterssonPositive.lean#L47-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaPeterssonPositive.lean#L47-L53

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainder_ne_zero (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaCuspidalRemainder q hq4≠0 := by sorry
