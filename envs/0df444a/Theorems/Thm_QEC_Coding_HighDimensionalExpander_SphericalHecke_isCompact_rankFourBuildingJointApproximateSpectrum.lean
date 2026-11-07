-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_isCompact_rankFourBuildingJointApproximateSpectrum
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.isCompact_rankFourBuildingJointApproximateSpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:15.489198+00:00
-- url     : https://prove2.me/theorems/8eb31887-d5d5-44ad-b4b3-2217b86613ef
-- title:
--   Spherical Hecke: is Compact rank Four Building Joint Approximate Spectrum
-- statement:
--   The Spherical Hecke construction uses the is Compact rank Four Building Joint Approximate Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1469-L1473
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1469-L1473

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.isCompact_rankFourBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] :
    IsCompact (RankFourBuildingJointApproximateSpectrum k) := by sorry
