-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_mul
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:41:44.643381+00:00
-- url     : https://prove2.me/theorems/d17f79a3-2823-4a72-b13c-9ec1ae3b47a6
-- title:
--   Spherical Hecke: local Unit Order mul
-- statement:
--   The Spherical Hecke construction uses the local Unit Order mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1708-L1712
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1708-L1712

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_mul
    {k : Type u} [Field k]
    (a b : Units (LocalFunctionField k)) :
    localUnitOrder (a * b) = localUnitOrder a + localUnitOrder b := by sorry
