-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_coordinateUniformizer_eq_one
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_coordinateUniformizer_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:44.983727+00:00
-- url     : https://prove2.me/theorems/4302a410-a2cb-45c5-b9ab-49b4963d1652
-- title:
--   Spherical Hecke: modular Character coordinate Uniformizer eq one
-- statement:
--   In positive rank, the modular character is one on every coordinate
--   uniformizer.  The proof uses all coordinates at once: their projective
--   product is scalar, while permutation conjugacy makes all character values
--   equal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L998-L1025
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L998-L1025

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_coordinateUniformizer_eq_one
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) (i : Fin d) :
    MeasureTheory.Measure.modularCharacter
        (coordinateUniformizerCoweight k d i) = 1 := by sorry
