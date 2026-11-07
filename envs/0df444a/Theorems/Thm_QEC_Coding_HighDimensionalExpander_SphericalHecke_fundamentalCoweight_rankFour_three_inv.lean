-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalCoweight_rankFour_three_inv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_rankFour_three_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:46.962757+00:00
-- url     : https://prove2.me/theorems/c9cd23b7-2dcf-4c6c-83f9-059f5c2d45ee
-- title:
--   Spherical Hecke: fundamental Coweight rank Four three inv
-- statement:
--   The Spherical Hecke construction uses the fundamental Coweight rank Four three inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3352-L3361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3352-L3361

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_rankFour_three_inv
    (k : Type u) [Field k] :
    (fundamentalCoweight k 4 3)⁻¹ =
      permutationCoweight k Fin.revPerm *
        fundamentalCoweight k 4 1 *
        (permutationCoweight k Fin.revPerm)⁻¹ := by sorry
