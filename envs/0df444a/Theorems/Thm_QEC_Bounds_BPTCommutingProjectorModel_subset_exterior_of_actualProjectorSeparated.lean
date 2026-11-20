-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_subset_exterior_of_actualProjectorSeparated
-- name    : QEC.Bounds.BPTCommutingProjectorModel.subset_exterior_of_actualProjectorSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:19:28.461181+00:00
-- url     : https://prove2.me/theorems/2d86daf7-07ff-424d-8974-8d1817f2191e
-- title:
--   BPTCommuting Projector Model: subset exterior of actual Projector Separated
-- statement:
--   The second source region is contained in `D = complement M1 \\ partialPlus M1`.
--   This is derived from actual projector support separation rather than a graph
--   distance convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L210-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L210-L223

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.subset_exterior_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right) :
    right ⊆ M.exterior left := by sorry
