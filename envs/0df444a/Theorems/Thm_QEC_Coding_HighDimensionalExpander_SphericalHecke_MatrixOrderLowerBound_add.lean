-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_add
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.MatrixOrderLowerBound.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:26.543258+00:00
-- url     : https://prove2.me/theorems/35f56b1a-a33d-45e1-a2ff-d84014993243
-- title:
--   Matrix Order Lower Bound: add
-- statement:
--   The Matrix Order Lower Bound construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1587-L1595
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1587-L1595

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.MatrixOrderLowerBound.add
    {k : Type u} [Field k] {d : ℕ} {m : WithTop ℤ}
    {A B : Matrix (Fin d) (Fin d) (LocalFunctionField k)}
    (hA : MatrixOrderLowerBound m A)
    (hB : MatrixOrderLowerBound m B) :
    MatrixOrderLowerBound m (A + B) := by sorry
