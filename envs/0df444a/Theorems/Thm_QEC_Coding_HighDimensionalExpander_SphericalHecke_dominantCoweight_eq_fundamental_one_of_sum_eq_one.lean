-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantCoweight_eq_fundamental_one_of_sum_eq_one
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_eq_fundamental_one_of_sum_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:56.255567+00:00
-- url     : https://prove2.me/theorems/60a18c0e-0e8e-4bb3-ada3-02d757c71a61
-- title:
--   Spherical Hecke: dominant Coweight eq fundamental one of sum eq one
-- statement:
--   A nonnegative dominant coweight in positive dimension whose coordinates
--   sum to one is the first fundamental coweight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2139-L2188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2139-L2188

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_eq_fundamental_one_of_sum_eq_one
    {d : ℕ} (hd : 0 < d) (weight : DominantCoweight d)
    (hsum : ∑ i, weight.exponent i = 1) :
    weight = fundamentalDominantCoweight d 1 := by sorry
