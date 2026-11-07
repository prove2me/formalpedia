-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityLatticeEndomorphism_mul_apply
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLatticeEndomorphism_mul_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:34:09.875445+00:00
-- url     : https://prove2.me/theorems/8e318843-1fde-4ee6-82c5-9437916f4266
-- title:
--   Cartwright Steger: infinity Lattice Endomorphism mul apply
-- statement:
--   The Cartwright Steger construction uses the infinity Lattice Endomorphism mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1020-L1031
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1020-L1031

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_mul

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLatticeEndomorphism_mul_apply
    (P : BasePrime) (r : Rank)
    (g h : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hg : PreservesInfinityCyclicLattice P r g)
    (hh : PreservesInfinityCyclicLattice P r h)
    (X : InfinityCyclicLattice P r) :
    infinityLatticeEndomorphism P r (g * h) (hg.mul P r hh) X =
      infinityLatticeEndomorphism P r g hg
        (infinityLatticeEndomorphism P r h hh X) := by sorry
