-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_buildingColoredAdjacencyOperatorOfInv_comp_single_apply
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_comp_single_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:44.989772+00:00
-- url     : https://prove2.me/theorems/7ca9d6a7-b2e0-4297-aad1-4a12cb9c1e65
-- title:
--   Spherical Hecke: building Colored Adjacency Operator Of Inv comp single apply
-- statement:
--   Composition of two graph adjacency operators on a vertex delta is the
--   actual Haar convolution coefficient at the corresponding relative group
--   element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L999-L1036
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L999-L1036

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_comp_single_apply
    (k : Type u) [Field k] [Finite k] (d r r' s s' : ℕ)
    (hrset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d r')
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d s')
    (z x : BuildingVertex k d) :
    (buildingColoredAdjacencyOperatorOfInv k d r r' hrset ∘L
        buildingColoredAdjacencyOperatorOfInv k d s s' hsset)
        (buildingVertexDelta k d z) x =
      (fundamentalHeckeFunction k d r *
        fundamentalHeckeFunction k d s) (x.out⁻¹ * z.out) := by sorry
