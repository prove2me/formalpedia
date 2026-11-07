-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankThree_two
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_rankThree_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:33:23.129197+00:00
-- url     : https://prove2.me/theorems/e7a4ca8e-3f48-470c-85f4-c80445d46e89
-- title:
--   Spherical Hecke: colored Adjacency Degree rank Three two
-- statement:
--   The Spherical Hecke construction uses the colored Adjacency Degree rank Three two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L767-L773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L767-L773

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_rankThree_two
    (k : Type*) [Field k] [Finite k] :
    coloredAdjacencyDegree k 3 2 = Nat.card k ^ 2 + Nat.card k + 1 := by sorry
