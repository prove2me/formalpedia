-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_shiftFour_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.shiftFour_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:02.824292+00:00
-- url     : https://prove2.me/theorems/cff83346-09e1-4a81-b055-aa20ba026ce0
-- title:
--   Cartwright Steger: shift Four pow
-- statement:
--   The Cartwright Steger construction uses the shift Four pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L101-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L101-L106

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.shiftFour_pow (K : Type*) [CommRing K] (a : K) :
    !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] ^ 4 =
      a • (1 : Matrix (Fin 4) (Fin 4) K) := by sorry
