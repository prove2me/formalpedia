-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_code_eq_cssCode
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodedCode_code_eq_cssCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:01:32.579501+00:00
-- url     : https://prove2.me/theorems/90c5621e-bc18-4cd0-aac0-d4e44afe87c8
-- title:
--   Ngu24 Binary: binary Encoded Code code eq css Code
-- statement:
--   The Ngu24 Binary construction uses the binary Encoded Code code eq css Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L228-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L228-L236

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

theorem QEC.Distillation.Ngu24Binary.binaryEncodedCode_code_eq_cssCode (i : Nat) :
    (binaryEncodedCode i).code = (binaryCSSCode i).stabilizer.code := by sorry
