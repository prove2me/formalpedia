-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_BC_jointEigenspaces_isInternal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorAB_BC_jointEigenspaces_isInternal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:55:41.076546+00:00
-- url     : https://prove2.me/theorems/7cdc4416-6ecc-46c3-9631-5c8a206f823a
-- title:
--   BPTCommuting Projector Model: projector AB BC joint Eigenspaces is Internal
-- statement:
--   The two overlapping source projectors admit a genuine finite-dimensional joint
--   spectral decomposition.  This is the spectral part of the source's boundary
--   decomposition step: the remaining BV03 work refines these joint sectors using
--   the two interaction algebras to obtain tensor factors on the boundary itself.
--   The present theorem is used to keep that refinement anchored in an actual
--   orthogonal direct-sum decomposition of the concrete finite register.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3161-L3169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3161-L3169

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorAB_BC_jointEigenspaces_isInternal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    DirectSum.IsInternal (fun eigenvalue : Complex × Complex =>
      Module.End.eigenspace (M.projectorAB region) eigenvalue.2 ⊓
        Module.End.eigenspace (M.projectorBC region) eigenvalue.1) := by sorry
