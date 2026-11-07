-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_hasUpperUnipotentInfinityResidue
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_hasUpperUnipotentInfinityResidue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:31:47.403031+00:00
-- url     : https://prove2.me/theorems/37582481-dde4-4353-a33a-01d72b305d3b
-- title:
--   Cartwright Steger: cartwright Steger Generator has Upper Unipotent Infinity Residue
-- statement:
--   Equation (9) proves the actual generator-level Definition 4.7
--   condition in the constructed infinity lattice and its `1/y` reduction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1321-L1351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1321-L1351

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_hasUpperUnipotentInfinityResidue
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    HasUpperUnipotentInfinityResidue P r
      (cartwrightStegerGenerator P r x) := by sorry
