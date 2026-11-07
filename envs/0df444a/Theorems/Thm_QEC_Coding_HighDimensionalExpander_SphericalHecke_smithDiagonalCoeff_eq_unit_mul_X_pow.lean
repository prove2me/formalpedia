-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithDiagonalCoeff_eq_unit_mul_X_pow
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.smithDiagonalCoeff_eq_unit_mul_X_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:02.624704+00:00
-- url     : https://prove2.me/theorems/8c2b823c-d5dd-482a-b3e2-e5c09d7c8c1e
-- title:
--   Spherical Hecke: smith Diagonal Coeff eq unit mul X pow
-- statement:
--   The Spherical Hecke construction uses the smith Diagonal Coeff eq unit mul X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L463-L473
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L463-L473

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.smithDiagonalCoeff_eq_unit_mul_X_pow
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) :
    smithDiagonalCoeff (k := k) (d := d) A i =
      (smithCoeffUnit (k := k) (d := d) A i : IntegerRing k) *
        PowerSeries.X ^ smithExponent (k := k) (d := d) A i := by sorry
