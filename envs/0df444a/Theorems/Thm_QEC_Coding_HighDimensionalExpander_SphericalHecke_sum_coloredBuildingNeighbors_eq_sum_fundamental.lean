-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_sum_coloredBuildingNeighbors_eq_sum_fundamental
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.sum_coloredBuildingNeighbors_eq_sum_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:02.866199+00:00
-- url     : https://prove2.me/theorems/ebd835f0-9ca1-495e-ab0e-9f4f48afc9ee
-- title:
--   Spherical Hecke: sum colored Building Neighbors eq sum fundamental
-- statement:
--   Reindex the actual neighbor sum at `x` by the construction-owned
--   fundamental right-cosets transported from the base vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L893-L901
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L893-L901

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.sum_coloredBuildingNeighbors_eq_sum_fundamental
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) (F : BuildingVertex k d → ℂ) :
    (∑ y : {y // ColoredBuildingAdjacent k d r x y}, F y) =
      ∑ q : {q // q ∈ fundamentalNeighborCosets k d r},
        F (x.out • q.1) := by sorry
