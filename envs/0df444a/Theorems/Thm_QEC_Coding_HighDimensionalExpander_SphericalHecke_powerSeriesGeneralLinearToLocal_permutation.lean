-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesGeneralLinearToLocal_permutation
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesGeneralLinearToLocal_permutation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:18.426807+00:00
-- url     : https://prove2.me/theorems/06cf55c1-13a4-4082-8971-f5e94dfa1c54
-- title:
--   Spherical Hecke: power Series General Linear To Local permutation
-- statement:
--   A permutation matrix over the power-series ring maps to the same
--   permutation matrix over the local field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2216-L2225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2216-L2225

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesGeneralLinearToLocal_permutation
    (k : Type u) [Field k] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    powerSeriesGeneralLinearToLocal k d
        (permutationGeneralLinear (IntegerRing k) σ) =
      permutationGeneralLinear (LocalFunctionField k) σ := by sorry
