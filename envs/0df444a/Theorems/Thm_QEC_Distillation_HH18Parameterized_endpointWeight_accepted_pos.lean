-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_pos
-- name    : QEC.Distillation.HH18Parameterized.endpointWeight_accepted_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:59:54.423225+00:00
-- url     : https://prove2.me/theorems/5e5de33b-b579-432a-8a04-e39ec2f4739c
-- title:
--   HH18 Parameterized: endpoint Weight accepted pos
-- statement:
--   The actual accepted endpoint has strictly positive Born mass for every
--   allowed independent diagonal resource family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L78-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L78-L83

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.endpointWeight_accepted_pos {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < endpointWeight h hdegree (noisyResources m w epsilon) .accepted := by sorry
