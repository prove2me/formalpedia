-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_sum_fundamentalHeckeFunction_comm
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.sum_fundamentalHeckeFunction_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:53:38.627026+00:00
-- url     : https://prove2.me/theorems/ab01e542-7b6f-4825-a259-332ca88c64a4
-- title:
--   Spherical Hecke: sum fundamental Hecke Function comm
-- statement:
--   The two finite fundamental-coset kernels commute pointwise, with all Haar
--   volumes already evaluated to one on the right-coset fibers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L872-L881
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L872-L881

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.sum_fundamentalHeckeFunction_comm
    (k : Type u) [Field k] [Finite k] (n r s : ℕ)
    (a : HeckeGroup k (n + 1)) :
    (∑ q ∈ fundamentalNeighborCosets k (n + 1) r,
        fundamentalHeckeFunction k (n + 1) s (q.out⁻¹ * a)) =
      ∑ q ∈ fundamentalNeighborCosets k (n + 1) s,
        fundamentalHeckeFunction k (n + 1) r (q.out⁻¹ * a) := by sorry
