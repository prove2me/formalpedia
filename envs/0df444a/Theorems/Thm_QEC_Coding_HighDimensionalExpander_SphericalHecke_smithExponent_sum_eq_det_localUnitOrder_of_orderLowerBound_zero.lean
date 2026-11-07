-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithExponent_sum_eq_det_localUnitOrder_of_orderLowerBound_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.smithExponent_sum_eq_det_localUnitOrder_of_orderLowerBound_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:57.988604+00:00
-- url     : https://prove2.me/theorems/1c595012-6fe8-4dbc-9557-5360ba31e72b
-- title:
--   Spherical Hecke: smith Exponent sum eq det local Unit Order of order Lower Bound zero
-- statement:
--   For an invertible local matrix whose entries are integral, the sum of
--   the constructive Smith exponents is exactly the local order of its
--   determinant.  No denominator-clearing shift remains.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1834-L1853
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1834-L1853

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.smithExponent_sum_eq_det_localUnitOrder_of_orderLowerBound_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k))
    (hA : MatrixOrderLowerBound 0
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) :
    (∑ i, (smithExponent (k := k) (d := d) A i : ℤ)) =
      localUnitOrder (Matrix.GeneralLinearGroup.det A) := by sorry
