-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankFour_two
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_rankFour_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:33.211116+00:00
-- url     : https://prove2.me/theorems/2b496587-23e4-4ff7-90fc-5282bda032f9
-- title:
--   Spherical Hecke: colored Adjacency Degree rank Four two
-- statement:
--   The Spherical Hecke construction uses the colored Adjacency Degree rank Four two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L784-L791
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L784-L791

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_rankFour_two
    (k : Type*) [Field k] [Finite k] :
    coloredAdjacencyDegree k 4 2 =
      (Nat.card k ^ 2 + 1) * (Nat.card k ^ 2 + Nat.card k + 1) := by sorry
