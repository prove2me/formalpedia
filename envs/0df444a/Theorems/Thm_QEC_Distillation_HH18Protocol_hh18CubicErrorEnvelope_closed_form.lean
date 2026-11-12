-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18CubicErrorEnvelope_closed_form
-- name    : QEC.Distillation.HH18Protocol.hh18CubicErrorEnvelope_closed_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:26:53.818186+00:00
-- url     : https://prove2.me/theorems/66bc4357-95ad-47dc-a530-6517198c5ba0
-- title:
--   HH18 Protocol: hh18 Cubic Error Envelope closed form
-- statement:
--   The HH18 Protocol construction uses the hh18 Cubic Error Envelope closed form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L397-L414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L397-L414

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

theorem QEC.Distillation.HH18Protocol.hh18CubicErrorEnvelope_closed_form
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    hh18IterationScale * hh18CubicErrorEnvelope epsilon depth =
      (hh18IterationScale * epsilon.1) ^ (3 ^ depth) := by sorry
