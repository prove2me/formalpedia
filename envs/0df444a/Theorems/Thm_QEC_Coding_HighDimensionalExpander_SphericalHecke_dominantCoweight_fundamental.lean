-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantCoweight_fundamental
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:47:07.153564+00:00
-- url     : https://prove2.me/theorems/803b89a5-ddfe-4a20-afe9-2e7819cfc63b
-- title:
--   Spherical Hecke: dominant Coweight fundamental
-- statement:
--   The Spherical Hecke construction uses the dominant Coweight fundamental property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2200-L2205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2200-L2205

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_fundamental
    (k : Type u) [Field k] (d r : ℕ) :
    dominantCoweight k (fundamentalDominantCoweight d r) =
      fundamentalCoweight k d r := by sorry
