-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_actualOutputError_exists_le
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSchedule_actualOutputError_exists_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:34:44.813344+00:00
-- url     : https://prove2.me/theorems/af9f39bb-82d0-4e21-a46f-7e895af1614b
-- title:
--   HH18 Protocol: hh18 Depth Schedule actual Output Error exists le
-- statement:
--   The actual physically reached errors are cofinal below every positive
--   target, by the compiled envelope comparison.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1552-L1561
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1552-L1561

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic

theorem QEC.Distillation.HH18Protocol.hh18DepthSchedule_actualOutputError_exists_le
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon)
    (target : ℝ) (htarget : 0 < target) :
    ∃ depth : Nat,
      hh18DepthScheduleActualOutputError epsilon hsmall depth ≤ target := by sorry
