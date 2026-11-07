-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_mul
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.MatrixOrderLowerBound.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:41:33.991326+00:00
-- url     : https://prove2.me/theorems/83a681fd-14ef-4005-8827-97536ae9e737
-- title:
--   Matrix Order Lower Bound: mul
-- statement:
--   The Matrix Order Lower Bound construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1574-L1585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1574-L1585

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.MatrixOrderLowerBound.mul
    {k : Type u} [Field k] {d : ℕ} {a b : WithTop ℤ}
    {A B : Matrix (Fin d) (Fin d) (LocalFunctionField k)}
    (hA : MatrixOrderLowerBound a A)
    (hB : MatrixOrderLowerBound b B) :
    MatrixOrderLowerBound (a + b) (A * B) := by sorry
