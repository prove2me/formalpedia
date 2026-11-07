-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityLatticeEndomorphism_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLatticeEndomorphism_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:34:51.059781+00:00
-- url     : https://prove2.me/theorems/dfc07520-d1da-44ac-9d31-5ca64d48d5c9
-- title:
--   Cartwright Steger: infinity Lattice Endomorphism injective
-- statement:
--   Although its inverse need not yet be known to preserve the lattice, the
--   induced lattice endomorphism is injective because conjugation is invertible
--   on the ambient matrix algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1007-L1018
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1007-L1018

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLatticeEndomorphism_injective
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hg : PreservesInfinityCyclicLattice P r g) :
    Function.Injective (infinityLatticeEndomorphism P r g hg) := by sorry
