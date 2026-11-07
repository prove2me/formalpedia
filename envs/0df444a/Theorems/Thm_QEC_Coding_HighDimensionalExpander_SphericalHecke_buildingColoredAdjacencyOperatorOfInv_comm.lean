-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_buildingColoredAdjacencyOperatorOfInv_comm
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:34:49.350194+00:00
-- url     : https://prove2.me/theorems/e8bf23d3-1459-4c9b-8678-2b00bba86dc7
-- title:
--   Spherical Hecke: building Colored Adjacency Operator Of Inv comm
-- statement:
--   All bounded color adjacency operators commute in positive rank, because
--   their matrix coefficients on the dense vertex-delta span are the coefficients
--   of the commutative spherical Hecke convolution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1041-L1077
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L1041-L1077

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_comm
    (k : Type u) [Field k] [Finite k] (n r r' s s' : ℕ)
    (hrset : (fundamentalDoubleCoset k (n + 1) r)⁻¹ =
      fundamentalDoubleCoset k (n + 1) r')
    (hsset : (fundamentalDoubleCoset k (n + 1) s)⁻¹ =
      fundamentalDoubleCoset k (n + 1) s') :
    buildingColoredAdjacencyOperatorOfInv k (n + 1) r r' hrset ∘L
        buildingColoredAdjacencyOperatorOfInv k (n + 1) s s' hsset =
      buildingColoredAdjacencyOperatorOfInv k (n + 1) s s' hsset ∘L
        buildingColoredAdjacencyOperatorOfInv k (n + 1) r r' hrset := by sorry
