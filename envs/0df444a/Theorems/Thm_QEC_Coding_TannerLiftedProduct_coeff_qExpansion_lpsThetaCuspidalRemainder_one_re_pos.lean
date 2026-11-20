-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaCuspidalRemainder_one_re_pos
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaCuspidalRemainder_one_re_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:34:36.1841+00:00
-- url     : https://prove2.me/theorems/482ef6b5-b131-416f-b3d8-9dc5c5da40d0
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Theta Cuspidal Remainder one re pos
-- statement:
--   The true first coefficient is positive: a norm-one representation exceeds the complete correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaPeterssonPositive.lean#L16-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaPeterssonPositive.lean#L16-L44

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaCuspidalRemainder_one_re_pos (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    0<(PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4))).re := by sorry
