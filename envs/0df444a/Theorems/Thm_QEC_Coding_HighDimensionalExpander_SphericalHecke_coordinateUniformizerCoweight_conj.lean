-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_conj
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:31.003748+00:00
-- url     : https://prove2.me/theorems/dc39f422-9f56-47c2-b7fd-90c2350abb7b
-- title:
--   Spherical Hecke: coordinate Uniformizer Coweight conj
-- statement:
--   Coordinate coweights are conjugate in the projective local group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L958-L965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L958-L965

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_conj
    (k : Type u) [Field k] {d : ℕ} (i j : Fin d) :
    permutationCoweight k (Equiv.swap i j) *
        coordinateUniformizerCoweight k d i *
        (permutationCoweight k (Equiv.swap i j))⁻¹ =
      coordinateUniformizerCoweight k d j := by sorry
