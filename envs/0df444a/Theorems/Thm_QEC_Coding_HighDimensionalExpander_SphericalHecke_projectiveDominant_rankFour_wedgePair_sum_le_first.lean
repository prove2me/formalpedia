-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_wedgePair_sum_le_first
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_wedgePair_sum_le_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:16.679035+00:00
-- url     : https://prove2.me/theorems/19b5c309-12e4-4b25-82d1-f1f14da7a84f
-- title:
--   Spherical Hecke: projective Dominant rank Four wedge Pair sum le first
-- statement:
--   The Spherical Hecke construction uses the projective Dominant rank Four wedge Pair sum le first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2922-L2936
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2922-L2936

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_wedgePair_sum_le_first
    (weight : ProjectiveDominantCoweight 3) (p : Fin 6) :
    weight.toDominant.exponent (rankFourWedgeFirst p) +
        weight.toDominant.exponent (rankFourWedgeSecond p) ≤
      weight.toDominant.exponent (0 : Fin 4) +
        weight.toDominant.exponent (1 : Fin 4) := by sorry
