-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonal_smithDiagonalCoeff_factorization
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonal_smithDiagonalCoeff_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:07.046618+00:00
-- url     : https://prove2.me/theorems/f044f98a-49ba-4e71-8990-2055359b7ae0
-- title:
--   Spherical Hecke: diagonal smith Diagonal Coeff factorization
-- statement:
--   The Spherical Hecke construction uses the diagonal smith Diagonal Coeff factorization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L491-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L491-L515

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonal_smithDiagonalCoeff_factorization
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) =
      (smithUnitGeneralLinear (k := k) (d := d) A :
        Matrix (Fin d) (Fin d) (IntegerRing k)) *
      smithPowerDiagonal (k := k) (d := d) A := by sorry
