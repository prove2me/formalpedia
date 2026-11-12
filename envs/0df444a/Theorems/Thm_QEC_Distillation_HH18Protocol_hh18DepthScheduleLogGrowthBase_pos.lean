-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleLogGrowthBase_pos
-- name    : QEC.Distillation.HH18Protocol.hh18DepthScheduleLogGrowthBase_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:29:48.813262+00:00
-- url     : https://prove2.me/theorems/995ed8bd-0a76-4770-a39c-e273837dc382
-- title:
--   HH18 Protocol: hh18 Depth Schedule Log Growth Base pos
-- statement:
--   The initial scaled physical error supplies a strictly positive logarithmic
--   growth base.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1330-L1338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1330-L1338

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

theorem QEC.Distillation.HH18Protocol.hh18DepthScheduleLogGrowthBase_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) :
    0 < hh18DepthScheduleLogGrowthBase epsilon := by sorry
