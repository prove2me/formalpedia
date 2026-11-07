-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerBMatrix_mem_cyclicAlgebra
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerBMatrix_mem_cyclicAlgebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:28:55.137086+00:00
-- url     : https://prove2.me/theorems/9f6890e2-09f8-41f3-a175-6f7d97c33df7
-- title:
--   Cartwright Steger: cartwright Steger BMatrix mem cyclic Algebra
-- statement:
--   The Cartwright Steger construction uses the cartwright Steger BMatrix mem cyclic Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L399-L403
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L399-L403

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerBMatrix_mem_cyclicAlgebra
    (P : BasePrime) (r : Rank) :
    cartwrightStegerBMatrix P r ∈ CyclicAlgebra P r := by sorry
