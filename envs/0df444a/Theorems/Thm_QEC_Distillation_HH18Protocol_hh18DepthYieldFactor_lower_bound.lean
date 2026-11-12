-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_lower_bound
-- name    : QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:32:10.906194+00:00
-- url     : https://prove2.me/theorems/9cc79a99-a32f-4418-8110-27347a7596c0
-- title:
--   HH18 Protocol: hh18 Depth Yield Factor lower bound
-- statement:
--   Every finite actual fresh-layer accounting product is at least one half.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L656-L710
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L656-L710

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

theorem QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_lower_bound
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (1 : ℝ) / 2 ≤ (hh18DepthYieldFactor epsilon hsmall depth : ℝ) := by sorry
