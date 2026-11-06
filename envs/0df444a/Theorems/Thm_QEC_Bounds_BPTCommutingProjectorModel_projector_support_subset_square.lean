-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projector_support_subset_square
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projector_support_subset_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:08:51.438001+00:00
-- url     : https://prove2.me/theorems/2d2288ea-bdae-49ca-96e4-94ef391e6835
-- title:
--   BPTCommuting Projector Model: projector support subset square
-- statement:
--   The recorded square cover applies to the actual projector's recorded support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L171-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L171-L173

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projector_support_subset_square (M : BPTCommutingProjectorModel L κ) (check : κ) :
    M.support check ⊆ L.lattice.square (M.squareOrigin check) M.interactionRange := by sorry
