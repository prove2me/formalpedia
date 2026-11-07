-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_setIntegral_fundamentalDoubleCoset_eq_sum_neighbors
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.setIntegral_fundamentalDoubleCoset_eq_sum_neighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:17.774807+00:00
-- url     : https://prove2.me/theorems/06542e0a-8808-403f-a33f-6bb73925b4a4
-- title:
--   Spherical Hecke: set Integral fundamental Double Coset eq sum neighbors
-- statement:
--   Haar integration over a fundamental double coset is exactly the finite
--   sum over the construction-owned neighbouring right cosets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L58-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L58-L121

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.setIntegral_fundamentalDoubleCoset_eq_sum_neighbors
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (F : HeckeGroup k d → ℂ) (hF : Continuous F)
    (hK : ∀ g q : HeckeGroup k d, q ∈ maximalCompact k d →
      F (g * q) = F g) :
    ∫ x in fundamentalDoubleCoset k d r, F x
        ∂normalizedLocalHaarMeasure k d =
      ∑ q ∈ fundamentalNeighborCosets k d r, F q.out := by sorry
