-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusDifferenceRange_ne_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusDifferenceRange_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:48.951582+00:00
-- url     : https://prove2.me/theorems/5dc815e3-3b10-4a98-b10b-bd2874508745
-- title:
--   Cartwright Steger: frobenius Difference Range ne top
-- statement:
--   The Frobenius-difference range is a proper subspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L43-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L43-L59

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusDifferenceRange_ne_top
    (P : BasePrime) (r : Rank) :
    frobeniusDifferenceRange P r ≠ ⊤ := by sorry
