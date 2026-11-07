-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_eq_ncard_neighbors
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_eq_ncard_neighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:41:04.119714+00:00
-- url     : https://prove2.me/theorems/9b8d5b2c-1fbf-4af9-8bfb-3a7f3c57825f
-- title:
--   Spherical Hecke: colored Adjacency Degree eq ncard neighbors
-- statement:
--   The Spherical Hecke construction uses the colored Adjacency Degree eq ncard neighbors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L536-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L536-L546

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_eq_ncard_neighbors
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    coloredAdjacencyDegree k d r =
      {x : BuildingVertex k d |
        ColoredBuildingAdjacent k d r (QuotientGroup.mk 1) x}.ncard := by sorry
