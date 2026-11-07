-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_inv_first_entry_order
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_inv_first_entry_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:05.757292+00:00
-- url     : https://prove2.me/theorems/75d5fd30-4dcc-4225-92fe-cb1da3947fb3
-- title:
--   Spherical Hecke: projective Dominant inv first entry order
-- statement:
--   The Spherical Hecke construction uses the projective Dominant inv first entry order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2086-L2098
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2086-L2098

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_inv_first_entry_order
    {k : Type u} [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    ((((dominantGeneralLinear k weight.toDominant)⁻¹ :
      GL (Fin (n + 1)) (LocalFunctionField k)) :
      Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) 0 0).orderTop =
      ((-(weight.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ) := by sorry
