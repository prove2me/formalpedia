-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_last_entry_order
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_last_entry_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:52.966192+00:00
-- url     : https://prove2.me/theorems/d0661c1f-a45a-427e-9d4e-ccc6050e6bfe
-- title:
--   Spherical Hecke: projective Dominant last entry order
-- statement:
--   The Spherical Hecke construction uses the projective Dominant last entry order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2021-L2027
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2021-L2027

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_last_entry_order
    {k : Type u} [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    ((dominantGeneralLinear k weight.toDominant :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (LocalFunctionField k))
        (Fin.last n) (Fin.last n)).orderTop = 0 := by sorry
