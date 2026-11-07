-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_onePlusY_eq_one_add_splittingY
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusY_eq_one_add_splittingY
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:23.632376+00:00
-- url     : https://prove2.me/theorems/c950799f-cab3-4b43-b1d5-3915885f7cc5
-- title:
--   Cartwright Steger: one Plus Y eq one add splitting Y
-- statement:
--   The Cartwright Steger construction uses the one Plus Y eq one add splitting Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L415-L417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L415-L417

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusY_eq_one_add_splittingY (P : BasePrime) (r : Rank) :
    onePlusY P r = 1 + splittingY P r := by sorry
