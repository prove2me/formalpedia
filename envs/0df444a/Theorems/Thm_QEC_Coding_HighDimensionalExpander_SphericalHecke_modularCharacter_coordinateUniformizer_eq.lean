-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_coordinateUniformizer_eq
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_coordinateUniformizer_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:46.389621+00:00
-- url     : https://prove2.me/theorems/b63b93fd-6411-4aa6-9c7b-73f54f3d5f81
-- title:
--   Spherical Hecke: modular Character coordinate Uniformizer eq
-- statement:
--   The modular character takes the same value on every one-coordinate
--   uniformizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L981-L992
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L981-L992

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_coordinateUniformizer_eq
    (k : Type u) [Field k] [Finite k] {d : ℕ} (i j : Fin d) :
    MeasureTheory.Measure.modularCharacter
        (coordinateUniformizerCoweight k d i) =
      MeasureTheory.Measure.modularCharacter
        (coordinateUniformizerCoweight k d j) := by sorry
