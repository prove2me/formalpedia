-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_iteration_rate_sum_le
-- name    : QEC.Distillation.HH18Protocol.iteration_rate_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:31:47.321071+00:00
-- url     : https://prove2.me/theorems/5f947b26-f204-46e3-b279-dedb39f7f3cf
-- title:
--   HH18 Protocol: iteration rate sum le
-- statement:
--   Summing only the finite actual stages is no larger than the same geometric
--   tail budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L551-L562
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L551-L562

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

theorem QEC.Distillation.HH18Protocol.iteration_rate_sum_le (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    ∑ stage : Fin depth, (hh18ErrorIteration epsilon hsmall stage.1).1 ≤
      (4 / 3 : ℝ) * epsilon.1 := by sorry
