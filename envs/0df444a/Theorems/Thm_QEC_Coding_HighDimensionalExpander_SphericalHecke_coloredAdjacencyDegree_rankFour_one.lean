-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankFour_one
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_rankFour_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:32:53.849623+00:00
-- url     : https://prove2.me/theorems/b4deb843-1c82-4ede-b70d-c125cc610129
-- title:
--   Spherical Hecke: colored Adjacency Degree rank Four one
-- statement:
--   The Spherical Hecke construction uses the colored Adjacency Degree rank Four one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L775-L782
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L775-L782

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_rankFour_one
    (k : Type*) [Field k] [Finite k] :
    coloredAdjacencyDegree k 4 1 =
      Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 := by sorry
