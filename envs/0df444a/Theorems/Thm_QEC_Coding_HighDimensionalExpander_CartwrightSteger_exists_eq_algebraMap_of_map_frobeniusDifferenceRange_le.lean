-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_eq_algebraMap_of_map_frobeniusDifferenceRange_le
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_eq_algebraMap_of_map_frobeniusDifferenceRange_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:53:02.402181+00:00
-- url     : https://prove2.me/theorems/79027686-bf88-497e-b302-8e54bd768979
-- title:
--   Cartwright Steger: exists eq algebra Map of map frobenius Difference Range le
-- statement:
--   The Cartwright Steger construction uses the exists eq algebra Map of map frobenius Difference Range le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L108-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean#L108-L122

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_eq_algebraMap_of_map_frobeniusDifferenceRange_le
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r)
    (hstable : (frobeniusDifferenceRange P r).map
        (constantMultiplicationLinearMap P r a) ≤
      frobeniusDifferenceRange P r) :
    ∃ c : BaseField P,
      a = algebraMap (BaseField P) (ConstantExtension P r) c := by sorry
