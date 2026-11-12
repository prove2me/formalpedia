-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_endpointWeight_rejected_eq_rawRejectMass
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.endpointWeight_rejected_eq_rawRejectMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:44:09.138751+00:00
-- url     : https://prove2.me/theorems/c27b5137-3dbd-4041-978d-f49eefa0a77b
-- title:
--   BH12 Protocol: endpoint Weight rejected eq raw Reject Mass
-- statement:
--   The rejected Born weight is exactly the complementary raw error-word mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1107-L1120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1107-L1120

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.endpointWeight_rejected_eq_rawRejectMass (q : Nat) (p : ErrorParameter) :
    endpointWeight q p .rejected = rawRejectMass q p := by sorry
