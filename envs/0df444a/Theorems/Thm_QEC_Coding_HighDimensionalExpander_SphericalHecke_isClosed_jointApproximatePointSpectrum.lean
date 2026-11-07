-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_isClosed_jointApproximatePointSpectrum
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.isClosed_jointApproximatePointSpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:37.562074+00:00
-- url     : https://prove2.me/theorems/e4544125-6148-44f4-a05b-5e167e0c56f3
-- title:
--   Spherical Hecke: is Closed joint Approximate Point Spectrum
-- statement:
--   For a finite operator family, the approximate joint spectrum is closed.
--   The proof uses one simultaneous coordinate neighborhood and retains the same
--   unit vector while moving the candidate eigenpacket to its limit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1290-L1326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1290-L1326

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.isClosed_jointApproximatePointSpectrum
    {ι E : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) :
    IsClosed (jointApproximatePointSpectrum A) := by sorry
