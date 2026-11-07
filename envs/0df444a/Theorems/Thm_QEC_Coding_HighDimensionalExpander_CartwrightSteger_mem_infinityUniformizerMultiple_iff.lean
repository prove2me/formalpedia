-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_infinityUniformizerMultiple_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_infinityUniformizerMultiple_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:19.260059+00:00
-- url     : https://prove2.me/theorems/b7f8cd14-710c-4366-9c19-6cee4d5fcc7c
-- title:
--   Cartwright Steger: mem infinity Uniformizer Multiple iff
-- statement:
--   The span presentation of the uniformizer multiple is exactly `t L`;
--   there are no additional elements hidden by the span.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1169-L1192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1169-L1192

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_infinityUniformizerMultiple_iff
    (P : BasePrime) (r : Rank)
    (X : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    X ∈ InfinityUniformizerMultiple P r ↔
      ∃ Y, Y ∈ InfinityCyclicLattice P r ∧
        X = (infinityUniformizer P r) • Y := by sorry
