-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalCoweight_rankFour_one_inv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_rankFour_one_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:47.838825+00:00
-- url     : https://prove2.me/theorems/38e66efb-571a-42f8-bae7-dd64df9f76fd
-- title:
--   Spherical Hecke: fundamental Coweight rank Four one inv
-- statement:
--   In `PGL₄`, inversion exchanges colors one and three.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3328-L3337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3328-L3337

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_rankFour_one_inv
    (k : Type u) [Field k] :
    (fundamentalCoweight k 4 1)⁻¹ =
      permutationCoweight k Fin.revPerm *
        fundamentalCoweight k 4 3 *
        (permutationCoweight k Fin.revPerm)⁻¹ := by sorry
