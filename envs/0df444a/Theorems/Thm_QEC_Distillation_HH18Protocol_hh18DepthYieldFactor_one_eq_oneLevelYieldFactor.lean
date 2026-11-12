-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_one_eq_oneLevelYieldFactor
-- name    : QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_one_eq_oneLevelYieldFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:47:32.255389+00:00
-- url     : https://prove2.me/theorems/98c72968-68fa-414b-a5ea-6b0c0f03cf11
-- title:
--   HH18 Protocol: hh18 Depth Yield Factor one eq one Level Yield Factor
-- statement:
--   The depth-one accounting factor is the actual one-level yield factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1123-L1134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1123-L1134

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

theorem QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_one_eq_oneLevelYieldFactor
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    (hh18DepthYieldFactor epsilon hsmall 1 : ℝ) =
      (oneLevelYieldFactor epsilon : ℝ) := by sorry
