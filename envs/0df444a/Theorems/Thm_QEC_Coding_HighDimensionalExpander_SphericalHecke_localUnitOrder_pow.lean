-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_pow
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:51.351987+00:00
-- url     : https://prove2.me/theorems/aa0314b6-041f-4841-a557-b8e79122ed1e
-- title:
--   Spherical Hecke: local Unit Order pow
-- statement:
--   The Spherical Hecke construction uses the local Unit Order pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1714-L1723
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1714-L1723

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_pow
    {k : Type u} [Field k]
    (a : Units (LocalFunctionField k)) (m : ℕ) :
    localUnitOrder (a ^ m) = m * localUnitOrder a := by sorry
