-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18ActualStageRun_successProbability
-- name    : QEC.Distillation.HH18Protocol.hh18ActualStageRun_successProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:26:23.162376+00:00
-- url     : https://prove2.me/theorems/4b131cbc-e942-4c12-bdeb-3aeb36ad0877
-- title:
--   HH18 Protocol: hh18 Actual Stage Run success Probability
-- statement:
--   An actual stage run retains exactly its physical accepted Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L370-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L370-L377

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

theorem QEC.Distillation.HH18Protocol.hh18ActualStageRun_successProbability
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18ActualStageRun epsilon hsmall depth).successProbability =
      rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by sorry
