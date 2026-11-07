-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_quotientFiber_isCompact
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.quotientFiber_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:52.607613+00:00
-- url     : https://prove2.me/theorems/3cb5d3db-0de0-40e9-89a5-1430d36e4e8a
-- title:
--   Spherical Hecke: quotient Fiber is Compact
-- statement:
--   A quotient fiber is an actual compact right coset of the maximal compact
--   subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L34-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L34-L54

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.quotientFiber_isCompact
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (q : BuildingVertex k d) :
    IsCompact
      ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q}) := by sorry
