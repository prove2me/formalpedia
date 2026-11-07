-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_inner_buildingColoredAdjacencyOperatorOfInv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_buildingColoredAdjacencyOperatorOfInv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:04.043643+00:00
-- url     : https://prove2.me/theorems/12ac420d-3efb-455b-b56e-9d6738df7377
-- title:
--   Spherical Hecke: inner building Colored Adjacency Operator Of Inv
-- statement:
--   Reversing the Cartan color gives the Hilbert-space adjoint relation for
--   the actual graph adjacency operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L732-L770
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean#L732-L770

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_buildingColoredAdjacencyOperatorOfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d r)
    (f g : BuildingL2 k d) :
    inner ℂ (buildingColoredAdjacencyOperatorOfInv k d r s hset f) g =
      inner ℂ f (buildingColoredAdjacencyOperatorOfInv k d s r hsset g) := by sorry
