-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_sum_le
-- name    : QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:04:00.392536+00:00
-- url     : https://prove2.me/theorems/6913cb91-2469-4622-9234-c2617ca33d6d
-- title:
--   HH18 Parameterized: routed Depth Error Envelope sum le
-- statement:
--   Summing only the finite uniform envelope is no larger than its geometric
--   tail budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L1004-L1017
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L1004-L1017

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_sum_le {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    ∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1 ≤
      (4 / 3 : ℝ) * epsilon.1 := by sorry
