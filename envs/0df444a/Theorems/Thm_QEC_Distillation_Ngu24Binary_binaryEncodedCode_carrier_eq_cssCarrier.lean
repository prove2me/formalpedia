-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_carrier_eq_cssCarrier
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodedCode_carrier_eq_cssCarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:52:56.983254+00:00
-- url     : https://prove2.me/theorems/63f4d50c-3195-4f75-805f-129637792358
-- title:
--   Ngu24 Binary: binary Encoded Code carrier eq css Carrier
-- statement:
--   The concrete encoder range is exactly the actual CSS common-fixed carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L223-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L223-L226

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCSSFieldWordFintype

theorem QEC.Distillation.Ngu24Binary.binaryEncodedCode_carrier_eq_cssCarrier (i : Nat) :
    (binaryEncodedCode i).code.carrier = (binaryCSSCode i).stabilizer.code.carrier := by sorry
