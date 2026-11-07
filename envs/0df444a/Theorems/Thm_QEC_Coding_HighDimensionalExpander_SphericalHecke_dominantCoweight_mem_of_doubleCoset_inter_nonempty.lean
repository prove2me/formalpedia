-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantCoweight_mem_of_doubleCoset_inter_nonempty
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_mem_of_doubleCoset_inter_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:41:56.827199+00:00
-- url     : https://prove2.me/theorems/0d19cc97-bf1b-4081-8e3a-b52992945d01
-- title:
--   Spherical Hecke: dominant Coweight mem of double Coset inter nonempty
-- statement:
--   If two Cartan double cosets meet, the diagonal representative of either
--   one lies in the other.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2494-L2510
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2494-L2510

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantCoweight_mem_of_doubleCoset_inter_nonempty
    (k : Type u) [Field k] {d : ℕ}
    (a b : DominantCoweight d)
    (hinter : (dominantDoubleCoset k a ∩
      dominantDoubleCoset k b).Nonempty) :
    dominantCoweight k a ∈ dominantDoubleCoset k b := by sorry
