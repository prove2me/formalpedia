-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_two
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:41:35.941281+00:00
-- url     : https://prove2.me/theorems/4d93822d-6de2-4a46-a521-fca7d3945398
-- title:
--   Spherical Hecke: normalized Local Haar Measure fundamental Double Coset rank Four two
-- statement:
--   The Spherical Hecke construction uses the normalized Local Haar Measure fundamental Double Coset rank Four two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L823-L828
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L823-L828

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_two
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 4 (fundamentalDoubleCoset k 4 2) =
      ((Nat.card k ^ 2 + 1) * (Nat.card k ^ 2 + Nat.card k + 1) : ℕ) := by sorry
