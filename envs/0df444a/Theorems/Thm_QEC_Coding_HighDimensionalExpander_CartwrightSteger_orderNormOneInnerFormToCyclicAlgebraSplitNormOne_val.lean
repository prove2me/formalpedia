-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormToCyclicAlgebraSplitNormOne_val
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormToCyclicAlgebraSplitNormOne_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:24:59.552538+00:00
-- url     : https://prove2.me/theorems/d661c25d-15a6-4fd9-9982-da57df7edbbd
-- title:
--   Cartwright Steger: order Norm One Inner Form To Cyclic Algebra Split Norm One val
-- statement:
--   The Cartwright Steger construction uses the order Norm One Inner Form To Cyclic Algebra Split Norm One val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/GlobalNormOneBridge.lean#L65-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/GlobalNormOneBridge.lean#L65-L71

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormToCyclicAlgebraSplitNormOne_val
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    (orderNormOneInnerFormToCyclicAlgebraSplitNormOne P r s :
        (CyclicAlgebra P r)ˣ) =
      orderUnitToCyclicUnit P r
        (orderNormOneInnerFormToOrderUnits P r s) := by sorry
