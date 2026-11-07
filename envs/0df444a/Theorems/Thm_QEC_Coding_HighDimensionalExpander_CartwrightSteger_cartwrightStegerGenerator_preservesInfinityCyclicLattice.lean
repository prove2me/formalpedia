-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_preservesInfinityCyclicLattice
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_preservesInfinityCyclicLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:31:43.475285+00:00
-- url     : https://prove2.me/theorems/6743a82d-3c7c-4532-a330-1c8721a72ab8
-- title:
--   Cartwright Steger: cartwright Steger Generator preserves Infinity Cyclic Lattice
-- statement:
--   Every actual Cartwright--Steger generator preserves the infinity cyclic
--   lattice.  This is the integral, group-stable content behind its displayed
--   equation-(9) formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L899-L934
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L899-L934

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_preservesInfinityCyclicLattice
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    PreservesInfinityCyclicLattice P r
      (cartwrightStegerGenerator P r x) := by sorry
