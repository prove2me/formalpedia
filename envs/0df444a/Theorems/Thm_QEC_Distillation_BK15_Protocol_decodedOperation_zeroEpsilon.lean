-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Protocol_decodedOperation_zeroEpsilon
-- name    : QEC.Distillation.BK15.Protocol.decodedOperation_zeroEpsilon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T02:07:52.972485+00:00
-- url     : https://prove2.me/theorems/a9ebf4b8-bce8-48f4-99ed-b3af262b8bd6
-- title:
--   Protocol: decoded Operation zero Epsilon
-- statement:
--   The complete concrete BK15 operation sends the closed zero-noise physical
--   input to the reported ideal `A₀` density after syndrome processing, correction,
--   total CSS decoding, and the logical one-qubit basis identification.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2760-L2769
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2760-L2769

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Protocol
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput
open scoped BigOperators TensorProduct
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.BK15.Protocol.decodedOperation_zeroEpsilon :
    decodedOperation.mapDensity (rawInput zeroEpsilon) = aZeroDensity := by sorry
