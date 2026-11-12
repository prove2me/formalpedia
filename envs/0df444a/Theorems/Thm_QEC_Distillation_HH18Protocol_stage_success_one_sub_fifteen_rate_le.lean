-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_stage_success_one_sub_fifteen_rate_le
-- name    : QEC.Distillation.HH18Protocol.stage_success_one_sub_fifteen_rate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:32:19.060403+00:00
-- url     : https://prove2.me/theorems/ee99e83f-6eb1-4c60-aee1-673a9a4a733c
-- title:
--   HH18 Protocol: stage success one sub fifteen rate le
-- statement:
--   The actual all-zero branch and Bernoulli's inequality give the literal
--   one-block loss estimate at every reached rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L573-L593
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L573-L593

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

theorem QEC.Distillation.HH18Protocol.stage_success_one_sub_fifteen_rate_le
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    1 - 15 * (hh18ErrorIteration epsilon hsmall depth).1 ≤
      rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by sorry
