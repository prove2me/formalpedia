-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_matrixClearingScalar_mul_eq_localCartanFactors
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.matrixClearingScalar_mul_eq_localCartanFactors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:32.792743+00:00
-- url     : https://prove2.me/theorems/a6d8a00a-5be9-4eb9-98ca-f7a17a180568
-- title:
--   Spherical Hecke: matrix Clearing Scalar mul eq local Cartan Factors
-- statement:
--   Exact local-field Cartan factorization before quotienting the common
--   denominator-clearing scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L622-L658
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L622-L658

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.matrixClearingScalar_mul_eq_localCartanFactors
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.GeneralLinearGroup.scalar (Fin d)
        (matrixClearingScalarUnit (k := k) (d := d) A) * A =
      smithLeftGeneralLinearLocal (k := k) (d := d) A *
        smithPowerGeneralLinearLocal (k := k) (d := d) A *
      (smithRightGeneralLinearLocal (k := k) (d := d) A)⁻¹ := by sorry
