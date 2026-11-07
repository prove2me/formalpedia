-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:29.727928+00:00
-- url     : https://prove2.me/theorems/5e98afe5-c223-49fe-8ee7-dd954e792653
-- title:
--   Spherical Hecke: scalar order eq zero of projective Dominant mem double Coset
-- statement:
--   Once both dominant types are scalar-normalized, the scalar appearing
--   when a projective double-coset equality is lifted to `GL` has Laurent order
--   zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2515-L2649
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2515-L2649

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.scalar_order_eq_zero_of_projectiveDominant_mem_doubleCoset
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b) :
    ∃ (left right :
        GL (Fin (n + 1)) (Valued.integer (LocalFunctionField k)))
      (c : Units (LocalFunctionField k)),
      localUnitOrder c = 0 ∧
      dominantGeneralLinear k a.toDominant =
        Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c *
          (integralGeneralLinearToLocal k (n + 1) left *
            dominantGeneralLinear k b.toDominant *
            integralGeneralLinearToLocal k (n + 1) right) := by sorry
