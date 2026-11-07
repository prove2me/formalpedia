-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusDifferenceLinearMap_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusDifferenceLinearMap_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:47.565194+00:00
-- url     : https://prove2.me/theorems/65e42086-72ae-47bb-8606-4d85952c1336
-- title:
--   Cartwright Steger: frobenius Difference Linear Map one
-- statement:
--   The Cartwright Steger construction uses the frobenius Difference Linear Map one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L37-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L37-L40

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusDifferenceLinearMap_one
    (P : BasePrime) (r : Rank) :
    frobeniusDifferenceLinearMap P r 1 = 0 := by sorry
