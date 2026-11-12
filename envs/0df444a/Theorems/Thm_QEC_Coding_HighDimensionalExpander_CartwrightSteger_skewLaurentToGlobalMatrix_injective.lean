-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:22:55.965684+00:00
-- url     : https://prove2.me/theorems/87adadfc-2f16-4732-ba0b-98a7d16bc577
-- title:
--   Cartwright Steger: skew Laurent To Global Matrix injective
-- statement:
--   The explicit global matrix representation of the integral skew Laurent
--   ring is faithful.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewFaithfulness.lean#L166-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewFaithfulness.lean#L166-L183

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewFaithfulness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (skewLaurentToGlobalMatrix P r) := by sorry
