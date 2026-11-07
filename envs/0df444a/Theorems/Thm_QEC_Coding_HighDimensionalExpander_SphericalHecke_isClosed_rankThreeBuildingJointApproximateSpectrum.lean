-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_isClosed_rankThreeBuildingJointApproximateSpectrum
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.isClosed_rankThreeBuildingJointApproximateSpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:04.629473+00:00
-- url     : https://prove2.me/theorems/0fba4fac-84f6-4cba-8380-838304c80671
-- title:
--   Spherical Hecke: is Closed rank Three Building Joint Approximate Spectrum
-- statement:
--   The Spherical Hecke construction uses the is Closed rank Three Building Joint Approximate Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1441-L1445
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1441-L1445

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.isClosed_rankThreeBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] :
    IsClosed (RankThreeBuildingJointApproximateSpectrum k) := by sorry
