-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProduct_mem_codeSpace
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_mem_codeSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:02.822524+00:00
-- url     : https://prove2.me/theorems/68f8d0eb-8f49-4c59-9690-d77881f6168b
-- title:
--   BPTCommuting Projector Model: projector Product mem code Space
-- statement:
--   The finite product maps every vector into the common-fixed code space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L341-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L341-L344

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_mem_codeSpace (M : BPTCommutingProjectorModel L κ)
    (vector : L.Register) : M.projectorProduct vector ∈ M.codeSpace.carrier := by sorry
