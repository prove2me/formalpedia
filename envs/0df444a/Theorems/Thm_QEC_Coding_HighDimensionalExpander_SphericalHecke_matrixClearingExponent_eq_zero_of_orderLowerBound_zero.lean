-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_matrixClearingExponent_eq_zero_of_orderLowerBound_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.matrixClearingExponent_eq_zero_of_orderLowerBound_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:22.069172+00:00
-- url     : https://prove2.me/theorems/1b72d371-46e5-4978-b3f3-99430f046cd4
-- title:
--   Spherical Hecke: matrix Clearing Exponent eq zero of order Lower Bound zero
-- statement:
--   An honestly integral local matrix requires no denominator-clearing
--   uniformizer power in the constructive Smith reduction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1547-L1558
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1547-L1558

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.matrixClearingExponent_eq_zero_of_orderLowerBound_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))
    (hA : MatrixOrderLowerBound 0 A) :
    matrixClearingExponent A = 0 := by sorry
