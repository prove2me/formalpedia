-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_isInvInvariant
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_isInvInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:35.946393+00:00
-- url     : https://prove2.me/theorems/86080219-45b4-43c5-a945-76cea892de1b
-- title:
--   Spherical Hecke: normalized Local Haar Measure is Inv Invariant
-- statement:
--   Normalized local Haar measure is invariant under inversion in positive
--   rank.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1198-L1218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1198-L1218

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_isInvInvariant
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) :
    MeasureTheory.Measure.IsInvInvariant
      (normalizedLocalHaarMeasure k d) := by sorry
