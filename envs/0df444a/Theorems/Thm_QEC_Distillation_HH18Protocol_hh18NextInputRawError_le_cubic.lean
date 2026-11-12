-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18NextInputRawError_le_cubic
-- name    : QEC.Distillation.HH18Protocol.hh18NextInputRawError_le_cubic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:04:13.637058+00:00
-- url     : https://prove2.me/theorems/195de321-96d9-4b9d-b557-56492e20cf79
-- title:
--   HH18 Protocol: hh18 Next Input Raw Error le cubic
-- statement:
--   The raw physical Born error inherits the cubic bound from the actual
--   decoded trace bridge and the registered accepted-residual endpoint bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/OutputHandoff.lean#L453-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/OutputHandoff.lean#L453-L466

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

theorem QEC.Distillation.HH18Protocol.hh18NextInputRawError_le_cubic
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18NextInputRawError epsilon ≤
      (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by sorry
