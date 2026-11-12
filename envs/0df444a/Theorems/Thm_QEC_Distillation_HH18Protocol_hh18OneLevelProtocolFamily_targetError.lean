-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18OneLevelProtocolFamily_targetError
-- name    : QEC.Distillation.HH18Protocol.hh18OneLevelProtocolFamily_targetError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:32:37.779211+00:00
-- url     : https://prove2.me/theorems/71c26f37-97bc-418f-a89c-2f02e59d4ed3
-- title:
--   HH18 Protocol: hh18 One Level Protocol Family target Error
-- statement:
--   The #458 target is the explicit cubic bound derived from the actual
--   accepted decoded output, not the protocol error repeated as a definition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L997-L1001
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L997-L1001

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

theorem QEC.Distillation.HH18Protocol.hh18OneLevelProtocolFamily_targetError
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (hh18OneLevelProtocolFamily epsilon).targetError PUnit.unit =
      (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by sorry
