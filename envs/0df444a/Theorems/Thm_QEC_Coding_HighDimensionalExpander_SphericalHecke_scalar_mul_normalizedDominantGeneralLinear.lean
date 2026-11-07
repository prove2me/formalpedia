-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_scalar_mul_normalizedDominantGeneralLinear
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.scalar_mul_normalizedDominantGeneralLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:47:28.101026+00:00
-- url     : https://prove2.me/theorems/9fd8d342-0d61-4b76-ac4b-7e908d657e9a
-- title:
--   Spherical Hecke: scalar mul normalized Dominant General Linear
-- statement:
--   Restoring the removed last exponent is multiplication by a scalar
--   matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1932-L1981
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1932-L1981

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.scalar_mul_normalizedDominantGeneralLinear
    (k : Type u) [Field k] {n : ℕ}
    (weight : DominantCoweight (n + 1)) :
    Matrix.GeneralLinearGroup.scalar (Fin (n + 1))
        (uniformizerUnit k ^ weight.exponent (Fin.last n)) *
      dominantGeneralLinear k (normalizeDominantCoweight weight).toDominant =
        dominantGeneralLinear k weight := by sorry
