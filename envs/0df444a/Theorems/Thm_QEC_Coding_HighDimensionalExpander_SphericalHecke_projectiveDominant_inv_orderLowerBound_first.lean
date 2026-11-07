-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_inv_orderLowerBound_first
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_inv_orderLowerBound_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:59.884238+00:00
-- url     : https://prove2.me/theorems/c5a25b8c-402c-4d9d-bfb0-e0f4d78a9d26
-- title:
--   Spherical Hecke: projective Dominant inv order Lower Bound first
-- statement:
--   The Spherical Hecke construction uses the projective Dominant inv order Lower Bound first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2060-L2084
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2060-L2084

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_inv_orderLowerBound_first
    {k : Type u} [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    MatrixOrderLowerBound
      ((-(weight.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ)
      (((dominantGeneralLinear k weight.toDominant)⁻¹ :
          GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by sorry
