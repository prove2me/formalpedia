-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredBuildingAdjacent_smul_fundamental_iff
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredBuildingAdjacent_smul_fundamental_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:44.540197+00:00
-- url     : https://prove2.me/theorems/63687b81-dc08-4c33-a9e5-0df1453318a3
-- title:
--   Spherical Hecke: colored Building Adjacent smul fundamental iff
-- statement:
--   In the transported fundamental-neighbor coordinates, adjacency to `z`
--   is membership of the exact relative element in the second Cartan double
--   coset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L950-L969
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L950-L969

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredBuildingAdjacent_smul_fundamental_iff
    (k : Type u) [Field k] [Finite k] (d s : ℕ)
    (x z : BuildingVertex k d)
    (q : BuildingVertex k d) :
    ColoredBuildingAdjacent k d s (x.out • q) z ↔
      q.out⁻¹ * x.out⁻¹ * z.out ∈ fundamentalDoubleCoset k d s := by sorry
