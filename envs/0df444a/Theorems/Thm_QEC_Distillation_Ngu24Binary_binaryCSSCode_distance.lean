-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCSSCode_distance
-- name    : QEC.Distillation.Ngu24Binary.binaryCSSCode_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:37:41.141026+00:00
-- url     : https://prove2.me/theorems/42d2607c-1c96-4236-8a70-e3cb121b1220
-- title:
--   Ngu24 Binary: binary CSSCode distance
-- statement:
--   The distance is an attained quantum distance on the actual CSS carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L53-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L53-L57

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter

theorem QEC.Distillation.Ngu24Binary.binaryCSSCode_distance (i : Nat) :
    QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i) ∧
      ¬ QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i + 1) := by sorry
