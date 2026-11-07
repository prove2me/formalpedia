-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:15.090193+00:00
-- url     : https://prove2.me/theorems/9bdbac13-0896-4329-88c7-dc2ad9a68a0c
-- title:
--   Spherical Hecke: projective Dominant rank Four first Two Sum le of mem double Coset
-- statement:
--   The sum of the two largest normalized Cartan exponents cannot increase
--   when a rank-four representative is placed in another normalized Cartan
--   double coset.  This is the first-entry valuation argument applied to the
--   second exterior-power representation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3034-L3136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3034-L3136

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_firstTwoSum_le_of_mem_doubleCoset
    (k : Type u) [Field k]
    (a b : ProjectiveDominantCoweight 3)
    (hmem : dominantCoweight k a.toDominant ∈
      projectiveDominantDoubleCoset k b) :
    a.toDominant.exponent (0 : Fin 4) +
        a.toDominant.exponent (1 : Fin 4) ≤
      b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4) := by sorry
