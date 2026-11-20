-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_recoverable_of_boundary_cover
-- name    : QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_recoverable_of_boundary_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:30:16.286401+00:00
-- url     : https://prove2.me/theorems/4ba42339-7fc6-448f-9f27-d955a9312c7e
-- title:
--   BPTCommuting Projector Model: external Boundary recoverable of boundary cover
-- statement:
--   The actual external projector boundary is recoverable whenever a recoverable
--   boundary-cover region contains it.  This is the exact monotonicity bridge for
--   the merged Disentangling Lemma, not a cardinality or graph-closure argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L1118-L1127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L1118-L1127

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

theorem QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_recoverable_of_boundary_cover
    (M : BPTCommutingProjectorModel L kappa) (region cover : Finset L.Site)
    (hcover : M.RegionErasureRecoverable cover)
    (hboundary : M.boundary region ⊆ cover) :
    M.RegionErasureRecoverable (M.externalBoundary region) := by sorry
