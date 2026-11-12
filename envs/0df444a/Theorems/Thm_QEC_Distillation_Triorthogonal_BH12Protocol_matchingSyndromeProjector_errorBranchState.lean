-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_matchingSyndromeProjector_errorBranchState
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.matchingSyndromeProjector_errorBranchState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:52:20.915581+00:00
-- url     : https://prove2.me/theorems/7c54532f-1661-43e2-9ccc-00ecf04f4c21
-- title:
--   BH12 Protocol: matching Syndrome Projector error Branch State
-- statement:
--   The matching full joint-syndrome projector fixes its physical branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L482-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L482-L490

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.Triorthogonal.BH12Protocol.matchingSyndromeProjector_errorBranchState {q : Nat}
    (error : PhysicalError q) :
    jointStabilizerProjector (xChecks q) (xChecks_commute q)
        (syndromeOfError error) (errorBranchState error) =
      errorBranchState error := by sorry
