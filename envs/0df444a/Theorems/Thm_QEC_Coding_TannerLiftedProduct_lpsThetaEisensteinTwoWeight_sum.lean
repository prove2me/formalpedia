-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinTwoWeight_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinTwoWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:36:37.069587+00:00
-- url     : https://prove2.me/theorems/ff90a46d-a2cb-44d4-99d2-d23c01cf3af6
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein Two Weight sum
-- statement:
--   The actual two-power weights have zero total, cancelling the untwisted constant contribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L31-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L31-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinTwoWeight_sum : (∑ a : Fin 5,lpsThetaEisensteinTwoWeight a)=0 := by sorry
