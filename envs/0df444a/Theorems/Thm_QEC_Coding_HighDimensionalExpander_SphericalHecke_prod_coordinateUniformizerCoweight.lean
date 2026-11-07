-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_prod_coordinateUniformizerCoweight
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerCoweight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:35.8292+00:00
-- url     : https://prove2.me/theorems/c50b2a6f-cec8-41a5-a686-86866d5b51a6
-- title:
--   Spherical Hecke: prod coordinate Uniformizer Coweight
-- statement:
--   Consequently, the product of all coordinate coweights is the identity in
--   the projective group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L866-L882
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L866-L882

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerCoweight
    (k : Type u) [Field k] (d : ℕ) :
    ((List.finRange d).map
        (coordinateUniformizerCoweight k d)).prod = 1 := by sorry
