-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_apply_mem_spectrum_of_mem_jointApproximatePointSpectrum
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.apply_mem_spectrum_of_mem_jointApproximatePointSpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:37.197842+00:00
-- url     : https://prove2.me/theorems/5a24007f-1948-4ff1-bd02-b8f3b112eb11
-- title:
--   Spherical Hecke: apply mem spectrum of mem joint Approximate Point Spectrum
-- statement:
--   Every coordinate of a simultaneous approximate eigenpacket lies in the
--   ordinary Banach-algebra spectrum of the corresponding bounded operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1359-L1412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1359-L1412

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.apply_mem_spectrum_of_mem_jointApproximatePointSpectrum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) (a : ι → ℂ)
    (ha : a ∈ jointApproximatePointSpectrum A) (i : ι) :
    a i ∈ spectrum ℂ (A i) := by sorry
