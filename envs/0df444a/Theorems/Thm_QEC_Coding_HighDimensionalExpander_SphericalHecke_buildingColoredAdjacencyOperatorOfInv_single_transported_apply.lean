-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_buildingColoredAdjacencyOperatorOfInv_single_transported_apply
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_single_transported_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:39.178816+00:00
-- url     : https://prove2.me/theorems/7ce1a0cb-7659-4d9d-a271-1ecc826c52cf
-- title:
--   Spherical Hecke: building Colored Adjacency Operator Of Inv single transported apply
-- statement:
--   A second-color adjacency applied to a delta, at a transported
--   first-color neighbor, is exactly the second fundamental Hecke indicator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L973-L994
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L973-L994

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_single_transported_apply
    (k : Type u) [Field k] [Finite k] (d r s t : ℕ)
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d t)
    (x z : BuildingVertex k d)
    (q : {q // q ∈ fundamentalNeighborCosets k d r}) :
    buildingColoredAdjacencyOperatorOfInv k d s t hsset
        (buildingVertexDelta k d z) (x.out • q.1) =
      fundamentalHeckeFunction k d s
        (q.1.out⁻¹ * x.out⁻¹ * z.out) := by sorry
