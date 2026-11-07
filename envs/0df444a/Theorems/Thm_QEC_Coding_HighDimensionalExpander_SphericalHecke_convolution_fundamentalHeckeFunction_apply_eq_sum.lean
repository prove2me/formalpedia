-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_convolution_fundamentalHeckeFunction_apply_eq_sum
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.convolution_fundamentalHeckeFunction_apply_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:33.623086+00:00
-- url     : https://prove2.me/theorems/b8a403ff-b702-4255-a7fb-dbb7b3af1b41
-- title:
--   Spherical Hecke: convolution fundamental Hecke Function apply eq sum
-- statement:
--   Haar convolution of two fundamental characteristic functions is the
--   finite right-coset sum that counts the corresponding two-step building
--   paths.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L844-L868
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L844-L868

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.convolution_fundamentalHeckeFunction_apply_eq_sum
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (a : HeckeGroup k d) :
    (fundamentalHeckeFunction k d r *
        fundamentalHeckeFunction k d s) a =
      ∑ q ∈ fundamentalNeighborCosets k d r,
        fundamentalHeckeFunction k d s (q.out⁻¹ * a) := by sorry
