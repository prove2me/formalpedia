-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantDoubleCoset_fundamental
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantDoubleCoset_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:40.379728+00:00
-- url     : https://prove2.me/theorems/9667b616-5b96-47d5-8358-259f3101bff3
-- title:
--   Spherical Hecke: projective Dominant Double Coset fundamental
-- statement:
--   The Spherical Hecke construction uses the projective Dominant Double Coset fundamental property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2393-L2398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2393-L2398

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantDoubleCoset_fundamental
    (k : Type u) [Field k] (n r : ℕ) (hr : r ≤ n) :
    projectiveDominantDoubleCoset k
        (fundamentalProjectiveDominantCoweight n r hr) =
      fundamentalDoubleCoset k (n + 1) r := by sorry
