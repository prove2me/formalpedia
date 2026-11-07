-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFour_jointApproximate_apply_mem_spectrum
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFour_jointApproximate_apply_mem_spectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:34.911323+00:00
-- url     : https://prove2.me/theorems/cdfde7a2-dea9-4770-85ec-d686db6987a7
-- title:
--   Spherical Hecke: rank Four joint Approximate apply mem spectrum
-- statement:
--   Every rank-four joint approximate eigenpacket projects to the ordinary
--   operator spectrum in all three actual colors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1477-L1483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1477-L1483

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFour_jointApproximate_apply_mem_spectrum
    (k : Type u) [Field k] [Finite k]
    (a : Fin 3 → ℂ) (ha : a ∈ RankFourBuildingJointApproximateSpectrum k)
    (color : Fin 3) :
    a color ∈ spectrum ℂ (rankFourBuildingAdjacencyFamily k color) := by sorry
