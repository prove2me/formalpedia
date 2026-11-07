-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_secondCompound_inv_first_entry_order
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_secondCompound_inv_first_entry_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:44:09.769599+00:00
-- url     : https://prove2.me/theorems/1254d234-76b6-47e4-81c7-800ccd629368
-- title:
--   Spherical Hecke: projective Dominant rank Four second Compound inv first entry order
-- statement:
--   The Spherical Hecke construction uses the projective Dominant rank Four second Compound inv first entry order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2986-L3028
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2986-L3028

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_secondCompound_inv_first_entry_order
    {k : Type u} [Field k]
    (weight : ProjectiveDominantCoweight 3) :
    (((((rankFourSecondCompoundGeneralLinear
        (dominantGeneralLinear k weight.toDominant))⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
      Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) 0 0).orderTop) =
      ((-((weight.toDominant.exponent (0 : Fin 4) +
        weight.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) :
        WithTop ℤ) := by sorry
