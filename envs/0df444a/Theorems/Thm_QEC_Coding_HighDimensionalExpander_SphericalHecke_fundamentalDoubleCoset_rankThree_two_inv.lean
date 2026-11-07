-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankThree_two_inv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalDoubleCoset_rankThree_two_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:57.472568+00:00
-- url     : https://prove2.me/theorems/a6e7f75c-6b62-40d4-8b59-be7f54323555
-- title:
--   Spherical Hecke: fundamental Double Coset rank Three two inv
-- statement:
--   The Spherical Hecke construction uses the fundamental Double Coset rank Three two inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3416-L3423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3416-L3423

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalDoubleCoset_rankThree_two_inv
    (k : Type u) [Field k] :
    (fundamentalDoubleCoset k 3 2)⁻¹ =
      fundamentalDoubleCoset k 3 1 := by sorry
