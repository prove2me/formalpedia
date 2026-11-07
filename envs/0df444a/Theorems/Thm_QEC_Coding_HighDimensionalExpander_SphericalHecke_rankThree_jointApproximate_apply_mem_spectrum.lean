-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThree_jointApproximate_apply_mem_spectrum
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThree_jointApproximate_apply_mem_spectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:15.243313+00:00
-- url     : https://prove2.me/theorems/8323bcb7-947c-4101-aa34-03a4c741c15c
-- title:
--   Spherical Hecke: rank Three joint Approximate apply mem spectrum
-- statement:
--   Every rank-three joint approximate eigenpacket projects to the ordinary
--   operator spectrum in both actual colors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1455-L1461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1455-L1461

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThree_jointApproximate_apply_mem_spectrum
    (k : Type u) [Field k] [Finite k]
    (a : Fin 2 → ℂ) (ha : a ∈ RankThreeBuildingJointApproximateSpectrum k)
    (color : Fin 2) :
    a color ∈ spectrum ℂ (rankThreeBuildingAdjacencyFamily k color) := by sorry
