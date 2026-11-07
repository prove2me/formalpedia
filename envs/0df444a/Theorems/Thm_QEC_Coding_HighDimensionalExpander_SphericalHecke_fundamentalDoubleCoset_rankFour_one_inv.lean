-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankFour_one_inv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalDoubleCoset_rankFour_one_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:58.223772+00:00
-- url     : https://prove2.me/theorems/8cbf69d0-30fc-45f8-b16f-bcdc7e9ba664
-- title:
--   Spherical Hecke: fundamental Double Coset rank Four one inv
-- statement:
--   The Spherical Hecke construction uses the fundamental Double Coset rank Four one inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3425-L3432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3425-L3432

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalDoubleCoset_rankFour_one_inv
    (k : Type u) [Field k] :
    (fundamentalDoubleCoset k 4 1)⁻¹ =
      fundamentalDoubleCoset k 4 3 := by sorry
