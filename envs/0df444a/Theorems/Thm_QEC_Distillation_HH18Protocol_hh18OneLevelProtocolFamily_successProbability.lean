-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18OneLevelProtocolFamily_successProbability
-- name    : QEC.Distillation.HH18Protocol.hh18OneLevelProtocolFamily_successProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:45:45.003271+00:00
-- url     : https://prove2.me/theorems/2f7ab689-5c6c-4ed1-a0e0-b570234da823
-- title:
--   HH18 Protocol: hh18 One Level Protocol Family success Probability
-- statement:
--   The #458 family stores the actual physical HH18 accepted Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1018-L1023
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1018-L1023

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

theorem QEC.Distillation.HH18Protocol.hh18OneLevelProtocolFamily_successProbability
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ((hh18OneLevelProtocolFamily epsilon).protocol PUnit.unit).run.successProbability =
      rawSuccessMass epsilon := by sorry
