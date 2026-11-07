-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_isCompact_rankThreeBuildingJointApproximateSpectrum
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.isCompact_rankThreeBuildingJointApproximateSpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:05.545395+00:00
-- url     : https://prove2.me/theorems/96346abe-d1c4-4520-bbeb-5248f2001838
-- title:
--   Spherical Hecke: is Compact rank Three Building Joint Approximate Spectrum
-- statement:
--   The Spherical Hecke construction uses the is Compact rank Three Building Joint Approximate Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1447-L1451
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1447-L1451

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.isCompact_rankThreeBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] :
    IsCompact (RankThreeBuildingJointApproximateSpectrum k) := by sorry
