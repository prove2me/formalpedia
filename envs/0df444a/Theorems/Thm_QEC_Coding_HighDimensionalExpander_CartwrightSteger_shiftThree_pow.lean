-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_shiftThree_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.shiftThree_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:47:56.769472+00:00
-- url     : https://prove2.me/theorems/d508e1b7-641c-4208-8c27-03e63eb7ab8a
-- title:
--   Cartwright Steger: shift Three pow
-- statement:
--   The Cartwright Steger construction uses the shift Three pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L94-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L94-L99

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.shiftThree_pow (K : Type*) [CommRing K] (a : K) :
    !![0, 0, a; 1, 0, 0; 0, 1, 0] ^ 3 =
      a • (1 : Matrix (Fin 3) (Fin 3) K) := by sorry
