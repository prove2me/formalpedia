-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_summable_inner_coloredBuildingEdge_target_source_of_inv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.summable_inner_coloredBuildingEdge_target_source_of_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:58.151573+00:00
-- url     : https://prove2.me/theorems/0314e1b4-5c41-4be9-835c-d866d296190d
-- title:
--   Spherical Hecke: summable inner colored Building Edge target source of inv
-- statement:
--   The edgewise matrix-coefficient series is absolutely summable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L719-L728
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L719-L728

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.summable_inner_coloredBuildingEdge_target_source_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f g : BuildingL2 k d) :
    Summable (fun e : ColoredBuildingEdge k d r ↦
      inner ℂ (f e.2.1) (g e.1)) := by sorry
