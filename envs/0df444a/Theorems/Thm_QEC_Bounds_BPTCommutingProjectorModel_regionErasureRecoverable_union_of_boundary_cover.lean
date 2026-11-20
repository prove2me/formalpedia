-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_union_of_boundary_cover
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_union_of_boundary_cover
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T06:29:10.864182+00:00
-- url     : https://prove2.me/theorems/3ed9f6b0-f905-48de-801f-6defd98dc3e0
-- title:
--   BPTCommuting Projector Model: region Erasure Recoverable union of boundary cover
-- statement:
--   BPT Corollary `cor:recursion` (`2Dgeneral_codes08.tex:454-459`).
--
--   For the source partition `A = M \\ B`, `B`, `C`,
--   `D = (M union C)^c`, compose the concrete preparation bridge with the typed
--   `B union C` recovery.  The only use of #388 is its actual boundary-supported
--   unitary and projector factorization, exposed through
--   `disentangled_prepareSelected_fixed`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L1138-L1175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L1138-L1175

import Definitions.Def_QEC_Bounds_BPTDisentangling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_union_of_boundary_cover
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hregion : M.RegionErasureRecoverable region)
    (hinside : inside ⊆ region)
    (houtside : outside ⊆ regionᶜ)
    (hcover : M.RegionErasureRecoverable (inside ∪ outside))
    (hboundary : M.boundary region ⊆ inside ∪ outside) :
    M.RegionErasureRecoverable (region ∪ outside) := by sorry
