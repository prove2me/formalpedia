-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveContragredient_preimage_maximalCompact
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveContragredient_preimage_maximalCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:06.060855+00:00
-- url     : https://prove2.me/theorems/cb4cee3e-fd01-452c-a690-96e22bdcbdd1
-- title:
--   Spherical Hecke: projective Contragredient preimage maximal Compact
-- statement:
--   The Spherical Hecke construction uses the projective Contragredient preimage maximal Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1351-L1361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1351-L1361

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveContragredient_preimage_maximalCompact
    {k : Type u} [Field k] {d : ℕ} :
    projectiveContragredientHom ⁻¹' (maximalCompact k d :
      Set PGL(Fin d, LocalFunctionField k)) = maximalCompact k d := by sorry
