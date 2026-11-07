-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantMatrix_fixedBasis_linearIndependent
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantMatrix_fixedBasis_linearIndependent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:34:47.500656+00:00
-- url     : https://prove2.me/theorems/6c1c53c7-40b2-4509-86b6-aabda4c85f80
-- title:
--   Cartwright Steger: constant Matrix fixed Basis linear Independent
-- statement:
--   The fixed constant-field basis becomes a splitting-field basis of the
--   diagonal matrices after applying all Frobenius coordinates.  Nondegeneracy
--   comes from the proved evaluation determinant, not from a supplied matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L247-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L247-L262

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantMatrix_fixedBasis_linearIndependent
    (P : BasePrime) (r : Rank) :
    LinearIndependent (SplittingFunctionField P r)
      (fun j : Fin r.matrixRank =>
        constantMatrix P r (constantBasis P r j)) := by sorry
