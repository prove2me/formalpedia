-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_buildingColoredAdjacencyOperatorOfInv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_buildingColoredAdjacencyOperatorOfInv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:34:16.878223+00:00
-- url     : https://prove2.me/theorems/14545644-6876-4bff-bc20-3ec36eeb5daa
-- title:
--   Spherical Hecke: adjoint building Colored Adjacency Operator Of Inv
-- statement:
--   The Hilbert adjoint is exactly the operator for the reverse Cartan color.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L773-L786
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L773-L786

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_buildingColoredAdjacencyOperatorOfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d r) :
    (buildingColoredAdjacencyOperatorOfInv k d r s hset)† =
      buildingColoredAdjacencyOperatorOfInv k d s r hsset := by sorry
