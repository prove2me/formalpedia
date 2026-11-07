-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:34:23.622241+00:00
-- url     : https://prove2.me/theorems/8951edf5-a284-4b85-b351-34d822887692
-- title:
--   Spherical Hecke: rank Four Building Adjacency Family zero
-- statement:
--   The Spherical Hecke construction uses the rank Four Building Adjacency Family zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1195-L1199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1195-L1199

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_zero
    (k : Type u) [Field k] [Finite k] :
    rankFourBuildingAdjacencyFamily k 0 =
      rankFourBuildingAdjacencyOne k := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_zero
