-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_eq_one
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:41:55.628383+00:00
-- url     : https://prove2.me/theorems/833c5f41-b356-4bb9-a3e3-1eca96498662
-- title:
--   Spherical Hecke: modular Character eq one
-- statement:
--   The modular character of the projective local group is trivial in every
--   positive rank.  This is the unimodularity statement needed for Haar
--   inversion: Cartan decomposition reduces an arbitrary element to two compact
--   factors and one Smith power coweight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1139-L1168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1139-L1168

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_eq_one
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d)
    (g : PGL(Fin d, LocalFunctionField k)) :
    MeasureTheory.Measure.modularCharacter g = 1 := by sorry
