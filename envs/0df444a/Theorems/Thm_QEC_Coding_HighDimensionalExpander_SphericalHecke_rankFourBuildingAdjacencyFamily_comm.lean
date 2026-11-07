-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_comm
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:53:45.626031+00:00
-- url     : https://prove2.me/theorems/3f65b9a4-015a-4516-886f-5e2137a51e76
-- title:
--   Spherical Hecke: rank Four Building Adjacency Family comm
-- statement:
--   The rank-four color family commutes pairwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1227-L1237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1227-L1237

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_comm
    (k : Type u) [Field k] [Finite k] (i j : Fin 3) :
    rankFourBuildingAdjacencyFamily k i ∘L
        rankFourBuildingAdjacencyFamily k j =
      rankFourBuildingAdjacencyFamily k j ∘L
        rankFourBuildingAdjacencyFamily k i := by sorry
