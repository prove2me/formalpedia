-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_iteration_rate_sum_with_tail_le
-- name    : QEC.Distillation.HH18Protocol.iteration_rate_sum_with_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:32:12.443655+00:00
-- url     : https://prove2.me/theorems/ee6bfa3e-f45e-4b8f-b5b6-dff95f2f265c
-- title:
--   HH18 Protocol: iteration rate sum with tail le
-- statement:
--   The contractive actual rates have a finite geometric tail bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L534-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L534-L547

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

theorem QEC.Distillation.HH18Protocol.iteration_rate_sum_with_tail_le (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (∑ stage : Fin depth, (hh18ErrorIteration epsilon hsmall stage.1).1) +
      (4 / 3 : ℝ) * (hh18ErrorIteration epsilon hsmall depth).1 ≤
        (4 / 3 : ℝ) * epsilon.1 := by sorry
