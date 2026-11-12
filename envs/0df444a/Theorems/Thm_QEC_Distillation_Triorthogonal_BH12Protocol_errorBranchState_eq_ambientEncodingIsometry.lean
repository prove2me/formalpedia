-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_errorBranchState_eq_ambientEncodingIsometry
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.errorBranchState_eq_ambientEncodingIsometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:09:52.937254+00:00
-- url     : https://prove2.me/theorems/b4e767b5-9650-4528-ba37-6f2b5e6026b7
-- title:
--   BH12 Protocol: error Branch State eq ambient Encoding Isometry
-- statement:
--   Every accepted physical error branch is the concrete encoding of the
--   logical product state labelled by its derived odd-row syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2865-L2900
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2865-L2900

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.errorBranchState_eq_ambientEncodingIsometry {q : Nat}
    (error : PhysicalError q) (haccept : Accepts error) :
    errorBranchState error =
      ambientEncodingIsometry q (logicalErrorState (logicalErrorWord error)) := by sorry
