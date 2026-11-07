-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyOne_comm_two
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyOne_comm_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:34:58.332996+00:00
-- url     : https://prove2.me/theorems/f31e61b9-0ba3-49e4-94d8-b8a69a5719d9
-- title:
--   Spherical Hecke: rank Three Building Adjacency One comm two
-- statement:
--   The two rank-three color adjacency operators commute.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1082-L1089
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1082-L1089

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyOne_comm_two
    (k : Type u) [Field k] [Finite k] :
    rankThreeBuildingAdjacencyOne k ∘L rankThreeBuildingAdjacencyTwo k =
      rankThreeBuildingAdjacencyTwo k ∘L rankThreeBuildingAdjacencyOne k := by sorry
