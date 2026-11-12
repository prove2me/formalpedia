-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthRoutedChildRun_eq_actualStageRun_succ
-- name    : QEC.Distillation.HH18Protocol.hh18DepthRoutedChildRun_eq_actualStageRun_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:30:51.443267+00:00
-- url     : https://prove2.me/theorems/24a97486-e795-4d3e-83cc-8a2453019c03
-- title:
--   HH18 Protocol: hh18 Depth Routed Child Run eq actual Stage Run succ
-- statement:
--   At every finite depth, the child run built from routed fresh parent
--   outputs is the actual next-stage HH18 run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L870-L877
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L870-L877

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

theorem QEC.Distillation.HH18Protocol.hh18DepthRoutedChildRun_eq_actualStageRun_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthRoutedChildRun epsilon hsmall depth =
      hh18ActualStageRun epsilon hsmall (depth + 1) := by sorry
