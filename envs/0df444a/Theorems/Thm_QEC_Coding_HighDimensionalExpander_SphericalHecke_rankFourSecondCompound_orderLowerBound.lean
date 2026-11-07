-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompound_orderLowerBound
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompound_orderLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:46.703343+00:00
-- url     : https://prove2.me/theorems/9ba70503-3879-4670-b929-616453afcea9
-- title:
--   Spherical Hecke: rank Four Second Compound order Lower Bound
-- statement:
--   The Spherical Hecke construction uses the rank Four Second Compound order Lower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2899-L2910
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2899-L2910

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompound_orderLowerBound
    {k : Type u} [Field k] {m : WithTop ℤ}
    {A : Matrix (Fin 4) (Fin 4) (LocalFunctionField k)}
    (hA : MatrixOrderLowerBound m A) :
    MatrixOrderLowerBound (m + m) (rankFourSecondCompound A) := by sorry
