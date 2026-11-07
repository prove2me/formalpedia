-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyOne_isStarNormal
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyOne_isStarNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:51.146754+00:00
-- url     : https://prove2.me/theorems/e528419a-ad19-40e2-9ba9-c104ff8a4fe0
-- title:
--   Spherical Hecke: rank Three Building Adjacency One is Star Normal
-- statement:
--   The first rank-three color adjacency operator is normal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1122-L1128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1122-L1128

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyOne_isStarNormal
    (k : Type u) [Field k] [Finite k] :
    IsStarNormal (rankThreeBuildingAdjacencyOne k) := by sorry
