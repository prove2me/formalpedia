-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyThree_isStarNormal
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyThree_isStarNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:56.126799+00:00
-- url     : https://prove2.me/theorems/529b1744-0581-431d-8d83-10fb1337d203
-- title:
--   Spherical Hecke: rank Four Building Adjacency Three is Star Normal
-- statement:
--   The third rank-four color adjacency operator is normal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1155-L1161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1155-L1161

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyThree_isStarNormal
    (k : Type u) [Field k] [Finite k] :
    IsStarNormal (rankFourBuildingAdjacencyThree k) := by sorry
