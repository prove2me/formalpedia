-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantGeneralLinear_fundamental
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantGeneralLinear_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:19.603167+00:00
-- url     : https://prove2.me/theorems/a9ebda34-87e5-431a-b7cd-d7fa81b04f48
-- title:
--   Spherical Hecke: dominant General Linear fundamental
-- statement:
--   The Spherical Hecke construction uses the dominant General Linear fundamental property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2190-L2198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2190-L2198

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantGeneralLinear_fundamental
    (k : Type u) [Field k] (d r : ℕ) :
    dominantGeneralLinear k (fundamentalDominantCoweight d r) =
      fundamentalDiagonal k d r := by sorry
