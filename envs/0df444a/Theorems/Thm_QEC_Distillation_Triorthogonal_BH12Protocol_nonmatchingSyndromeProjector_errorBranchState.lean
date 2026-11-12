-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_nonmatchingSyndromeProjector_errorBranchState
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.nonmatchingSyndromeProjector_errorBranchState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:58:44.670757+00:00
-- url     : https://prove2.me/theorems/7115c954-5508-49a4-b025-fdd6684c2dbd
-- title:
--   BH12 Protocol: nonmatching Syndrome Projector error Branch State
-- statement:
--   Every nonmatching full syndrome annihilates the branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L493-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L493-L502

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.nonmatchingSyndromeProjector_errorBranchState {q : Nat}
    (error : PhysicalError q) (syndrome : Syndrome)
    (hne : syndrome ≠ syndromeOfError error) :
    jointStabilizerProjector (xChecks q) (xChecks_commute q)
        syndrome (errorBranchState error) = 0 := by sorry
