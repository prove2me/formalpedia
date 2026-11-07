-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompound_diagonal
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompound_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:56.773745+00:00
-- url     : https://prove2.me/theorems/8fcc90cb-578e-4b1e-98c7-ad634d25b492
-- title:
--   Spherical Hecke: rank Four Second Compound diagonal
-- statement:
--   The Spherical Hecke construction uses the rank Four Second Compound diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2912-L2920
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2912-L2920

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompound_diagonal
    {R : Type u} [CommRing R] (v : Fin 4 → R) :
    rankFourSecondCompound (Matrix.diagonal v) =
      Matrix.diagonal (fun p ↦
        v (rankFourWedgeFirst p) * v (rankFourWedgeSecond p)) := by sorry
