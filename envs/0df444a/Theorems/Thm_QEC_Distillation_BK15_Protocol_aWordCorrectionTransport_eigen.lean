-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Protocol_aWordCorrectionTransport_eigen
-- name    : QEC.Distillation.BK15.Protocol.aWordCorrectionTransport_eigen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T02:07:53.620274+00:00
-- url     : https://prove2.me/theorems/fc57b522-bfbc-4d6a-857e-1ae0d316ddb1
-- title:
--   Protocol: a Word Correction Transport eigen
-- statement:
--   The physical correction has the source binary character on every
--   A-error-word basis vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L415-L429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L415-L429

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
set_option maxRecDepth 65536

theorem QEC.Distillation.BK15.Protocol.aWordCorrectionTransport_eigen (word error : Word) :
    aWordCorrectionTransport word (bk15ErrorWordState error) =
      binaryPhaseScalar (word ⬝ᵥ error) • bk15ErrorWordState error := by sorry
