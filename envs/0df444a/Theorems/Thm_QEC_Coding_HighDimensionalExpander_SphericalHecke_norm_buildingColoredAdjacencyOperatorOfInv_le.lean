-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_norm_buildingColoredAdjacencyOperatorOfInv_le
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.norm_buildingColoredAdjacencyOperatorOfInv_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:34:27.088673+00:00
-- url     : https://prove2.me/theorems/a4b35c1d-16a0-4739-9408-4fdf1dfc2b9d
-- title:
--   Spherical Hecke: norm building Colored Adjacency Operator Of Inv le
-- statement:
--   Operator-norm form of the reverse-degree bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L536-L545
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L536-L545

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.norm_buildingColoredAdjacencyOperatorOfInv_le
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    ‖buildingColoredAdjacencyOperatorOfInv k d r s hset‖ ≤
      Real.sqrt ((coloredAdjacencyDegree k d r : ℝ) *
        coloredAdjacencyDegree k d s) := by sorry
