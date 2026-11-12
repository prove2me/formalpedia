-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18NextInputRawError_le_outputTrace
-- name    : QEC.Distillation.HH18Protocol.hh18NextInputRawError_le_outputTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:37:41.551372+00:00
-- url     : https://prove2.me/theorems/ab9c9613-f5f0-43cd-912c-9daf24fa89d2
-- title:
--   HH18 Protocol: hh18 Next Input Raw Error le output Trace
-- statement:
--   The literal physical negative-A Born error is bounded by the actual
--   decoded accepted-output trace error on the logical carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/OutputHandoff.lean#L404-L449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/OutputHandoff.lean#L404-L449

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable

theorem QEC.Distillation.HH18Protocol.hh18NextInputRawError_le_outputTrace
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18NextInputRawError epsilon ≤
      hh18OutputTraceError
        (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
        idealLogicalTOutput := by sorry
