-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderInnerFormToOrderUnits_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderInnerFormToOrderUnits_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:24:44.850513+00:00
-- url     : https://prove2.me/theorems/a928c1d8-8e7a-4035-aa34-7035162e483f
-- title:
--   Cartwright Steger: order Inner Form To Order Units surjective
-- statement:
--   The split-coordinate full inner form is not merely a selected subgroup:
--   it covers every unit of the actual Cartwright--Steger arithmetic order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/SplitCoordinates.lean#L102-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/SplitCoordinates.lean#L102-L166

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderInnerFormToOrderUnits_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderInnerFormToOrderUnits P r) := by sorry
