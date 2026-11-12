-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_endpointWeight_accepted_eq_rawSuccessMass
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.endpointWeight_accepted_eq_rawSuccessMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:53:03.213204+00:00
-- url     : https://prove2.me/theorems/d32b692f-5286-46e0-b814-e9771801859d
-- title:
--   BH12 Protocol: endpoint Weight accepted eq raw Success Mass
-- statement:
--   The accepted Born weight is exactly the raw accepted error-word mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1091-L1104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1091-L1104

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.endpointWeight_accepted_eq_rawSuccessMass (q : Nat) (p : ErrorParameter) :
    endpointWeight q p .accepted = rawSuccessMass q p := by sorry
