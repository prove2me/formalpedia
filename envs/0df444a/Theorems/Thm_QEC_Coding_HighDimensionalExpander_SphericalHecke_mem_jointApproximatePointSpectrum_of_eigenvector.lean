-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mem_jointApproximatePointSpectrum_of_eigenvector
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.mem_jointApproximatePointSpectrum_of_eigenvector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:06.516778+00:00
-- url     : https://prove2.me/theorems/bac7eb83-1f61-4157-aa2e-fb3d0c4a338c
-- title:
--   Spherical Hecke: mem joint Approximate Point Spectrum of eigenvector
-- statement:
--   A common unit eigenvector gives an approximate joint eigenpacket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1276-L1285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1276-L1285

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.mem_jointApproximatePointSpectrum_of_eigenvector
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) (a : ι → ℂ) (v : E)
    (hv : ‖v‖ = 1) (heigen : ∀ i, A i v = a i • v) :
    a ∈ jointApproximatePointSpectrum A := by sorry
