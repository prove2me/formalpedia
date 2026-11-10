-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_measurementDistance
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodedCode_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:47:36.779255+00:00
-- url     : https://prove2.me/theorems/0d30ca5c-45ce-40eb-86f0-eefe5de8593f
-- title:
--   Ngu24 Binary: binary Encoded Code measurement Distance
-- statement:
--   The Ngu24 Binary construction uses the binary Encoded Code measurement Distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryDistance.lean#L97-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryDistance.lean#L97-L102

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable {J : Type} [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_9a39a2a69e_41

theorem QEC.Distillation.Ngu24Binary.binaryEncodedCode_measurementDistance (i : Nat) :
    QuditSubsystem.BPTMeasurementDistance (binaryEncodedCode i).code (f256QuditDistanceBound i) := by sorry
