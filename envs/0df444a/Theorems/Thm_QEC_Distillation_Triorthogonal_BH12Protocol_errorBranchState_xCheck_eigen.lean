-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_errorBranchState_xCheck_eigen
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.errorBranchState_xCheck_eigen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:58:11.100141+00:00
-- url     : https://prove2.me/theorems/4346bf10-0eac-4dac-860f-53ebc93aba5f
-- title:
--   BH12 Protocol: error Branch State x Check eigen
-- statement:
--   Every error branch lies in the simultaneous eigenspace of its literal syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L436-L479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L436-L479

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.errorBranchState_xCheck_eigen {q : Nat} (error : PhysicalError q)
    (check : EvenRow) :
    toHermitianQubitOperator (xChecks q check) (errorBranchState error) =
      (syndromeOfError error check).sign • errorBranchState error := by sorry
