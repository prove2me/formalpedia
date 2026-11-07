-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_eq_frobeniusSymm_of_map_frobeniusDifferenceRange_le
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_frobeniusSymm_of_map_frobeniusDifferenceRange_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:56.091636+00:00
-- url     : https://prove2.me/theorems/09264b65-31e2-4792-9a15-0b7df0795ff4
-- title:
--   Cartwright Steger: eq frobenius Symm of map frobenius Difference Range le
-- statement:
--   Only Frobenius-fixed scalars can preserve the Frobenius-difference
--   hyperplane under multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L79-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L79-L106

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_frobeniusSymm_of_map_frobeniusDifferenceRange_le
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r)
    (hstable : (frobeniusDifferenceRange P r).map
        (constantMultiplicationLinearMap P r a) ≤
      frobeniusDifferenceRange P r) :
    (constantFrobenius P r).symm a = a := by sorry
