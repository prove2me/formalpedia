-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_buildingColoredAdjacencyOperatorOfInv_single_apply_of_adjacent
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_single_apply_of_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:11.627191+00:00
-- url     : https://prove2.me/theorems/8527c979-9cc9-41f7-b8e4-cda84b8c0184
-- title:
--   Spherical Hecke: building Colored Adjacency Operator Of Inv single apply of adjacent
-- statement:
--   On an adjacent delta vertex, a color adjacency operator has value one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L911-L927
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L911-L927

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_single_apply_of_adjacent
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (z x : BuildingVertex k d)
    (hxz : ColoredBuildingAdjacent k d r x z) :
    buildingColoredAdjacencyOperatorOfInv k d r s hset
        (buildingVertexDelta k d z) x = 1 := by sorry
