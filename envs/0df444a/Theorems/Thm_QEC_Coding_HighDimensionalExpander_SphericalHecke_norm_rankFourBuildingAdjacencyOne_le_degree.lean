-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_norm_rankFourBuildingAdjacencyOne_le_degree
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.norm_rankFourBuildingAdjacencyOne_le_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:53:18.523194+00:00
-- url     : https://prove2.me/theorems/a6363ac8-b4cb-42e8-842a-2909cec161fc
-- title:
--   Spherical Hecke: norm rank Four Building Adjacency One le degree
-- statement:
--   The Spherical Hecke construction uses the norm rank Four Building Adjacency One le degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L649-L662
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L649-L662

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.norm_rankFourBuildingAdjacencyOne_le_degree
    (k : Type u) [Field k] [Finite k] :
    ‖rankFourBuildingAdjacencyOne k‖ ≤
      coloredAdjacencyDegree k 4 1 := by sorry
