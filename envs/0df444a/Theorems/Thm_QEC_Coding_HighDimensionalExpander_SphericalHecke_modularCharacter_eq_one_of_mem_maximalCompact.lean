-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_eq_one_of_mem_maximalCompact
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_eq_one_of_mem_maximalCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:26.786917+00:00
-- url     : https://prove2.me/theorems/4c10202a-ed04-4091-b095-8c6d98db5043
-- title:
--   Spherical Hecke: modular Character eq one of mem maximal Compact
-- statement:
--   The modular character is one on the normalized maximal compact subgroup.
--   This is proved by evaluating right translation on `K`, whose Haar measure is
--   exactly one, rather than by assuming continuity of the modular character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L765-L799
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L765-L799

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_eq_one_of_mem_maximalCompact
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (h : PGL(Fin d, LocalFunctionField k)) (hh : h ∈ maximalCompact k d) :
    MeasureTheory.Measure.modularCharacter h = 1 := by sorry
