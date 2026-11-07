-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_mul
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:36.493347+00:00
-- url     : https://prove2.me/theorems/1bda69a0-42ac-4c5e-a5a2-2499614127b9
-- title:
--   Spherical Hecke: projective Transpose mul
-- statement:
--   The Spherical Hecke construction uses the projective Transpose mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1412-L1417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1412-L1417

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_mul
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (g h : PGL(n, R)) :
    projectiveTranspose (g * h) =
      projectiveTranspose h * projectiveTranspose g := by sorry
