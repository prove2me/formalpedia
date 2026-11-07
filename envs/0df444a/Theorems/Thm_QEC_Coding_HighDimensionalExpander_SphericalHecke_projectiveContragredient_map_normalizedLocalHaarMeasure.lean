-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveContragredient_map_normalizedLocalHaarMeasure
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveContragredient_map_normalizedLocalHaarMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:02.619237+00:00
-- url     : https://prove2.me/theorems/ed28719f-f0b8-4aec-912b-0f55f234fea9
-- title:
--   Spherical Hecke: projective Contragredient map normalized Local Haar Measure
-- statement:
--   The Spherical Hecke construction uses the projective Contragredient map normalized Local Haar Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1363-L1395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1363-L1395

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveContragredient_map_normalizedLocalHaarMeasure
    {k : Type u} [Field k] [Finite k] {d : ℕ} :
    MeasureTheory.Measure.map projectiveContragredientHom
        (normalizedLocalHaarMeasure k d) =
      normalizedLocalHaarMeasure k d := by sorry
