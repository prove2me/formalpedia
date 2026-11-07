-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_one
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:41:22.016215+00:00
-- url     : https://prove2.me/theorems/116b78da-2369-4f7b-985a-9a001eab1baf
-- title:
--   Spherical Hecke: normalized Local Haar Measure fundamental Double Coset rank Four one
-- statement:
--   The Spherical Hecke construction uses the normalized Local Haar Measure fundamental Double Coset rank Four one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L816-L821
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L816-L821

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_one
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 4 (fundamentalDoubleCoset k 4 1) =
      (Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 : ℕ) := by sorry
