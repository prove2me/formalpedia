-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_measurePreserving
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:08.896358+00:00
-- url     : https://prove2.me/theorems/7d4161c6-c867-4fab-9203-fb7da7f51a6f
-- title:
--   Spherical Hecke: projective Transpose measure Preserving
-- statement:
--   The Spherical Hecke construction uses the projective Transpose measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1447-L1457
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1447-L1457

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_measurePreserving
    {k : Type u} [Field k] [Finite k] {d : ℕ} (hd : 0 < d) :
    MeasureTheory.MeasurePreserving projectiveTranspose
      (normalizedLocalHaarMeasure k d)
      (normalizedLocalHaarMeasure k d) := by sorry
