-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithDominantCoweight_exponent_sum
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.smithDominantCoweight_exponent_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:51.049209+00:00
-- url     : https://prove2.me/theorems/103cc65b-9d78-41bb-9db4-a512f452beff
-- title:
--   Spherical Hecke: smith Dominant Coweight exponent sum
-- statement:
--   Sorting the Smith exponents into dominant order preserves their sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1878-L1887
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1878-L1887

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.smithDominantCoweight_exponent_sum
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (∑ i, ((smithDominantCoweight A).exponent i : ℤ)) =
      ∑ i, (smithExponent (k := k) (d := d) A i : ℤ) := by sorry
