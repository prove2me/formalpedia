-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_prod_coordinateUniformizerCoweight_pow_eq_smithPower
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerCoweight_pow_eq_smithPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:57.980258+00:00
-- url     : https://prove2.me/theorems/8a90fc48-fe7f-4191-90a1-e05f013e7dd3
-- title:
--   Spherical Hecke: prod coordinate Uniformizer Coweight pow eq smith Power
-- statement:
--   Projective form of the coordinate factorization of a Smith power
--   coweight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1074-L1103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1074-L1103

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerCoweight_pow_eq_smithPower
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    ((List.finRange d).map (fun i =>
        coordinateUniformizerCoweight k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
      smithPowerCoweight (k := k) (d := d) A := by sorry
