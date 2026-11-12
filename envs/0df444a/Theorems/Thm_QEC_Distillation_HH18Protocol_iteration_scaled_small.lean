-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_iteration_scaled_small
-- name    : QEC.Distillation.HH18Protocol.iteration_scaled_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:29:27.121744+00:00
-- url     : https://prove2.me/theorems/ceace13c-f7b8-464c-b95c-7b693f59b84e
-- title:
--   HH18 Protocol: iteration scaled small
-- statement:
--   The public cubic envelope recovers the private iterator invariant without
--   referring to its hidden implementation state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L461-L482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L461-L482

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

theorem QEC.Distillation.HH18Protocol.iteration_scaled_small (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1 ≤ 1 / 2 := by sorry
