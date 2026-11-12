-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthInputSlots_card
-- name    : QEC.Distillation.HH18Protocol.hh18DepthInputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:27:28.139398+00:00
-- url     : https://prove2.me/theorems/5d484435-7ea1-4859-a75c-2dfb184a2f7a
-- title:
--   HH18 Protocol: hh18 Depth Input Slots card
-- statement:
--   The HH18 Protocol construction uses the hh18 Depth Input Slots card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L451-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L451-L453

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

theorem QEC.Distillation.HH18Protocol.hh18DepthInputSlots_card (depth : Nat) :
    Fintype.card (hh18DepthInputSlots depth) = 15 ^ depth := by sorry
