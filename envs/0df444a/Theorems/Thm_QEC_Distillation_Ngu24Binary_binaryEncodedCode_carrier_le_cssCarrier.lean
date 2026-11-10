-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_carrier_le_cssCarrier
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodedCode_carrier_le_cssCarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:52:29.230401+00:00
-- url     : https://prove2.me/theorems/581dfd0a-c004-4c17-9b84-073febd8a45b
-- title:
--   Ngu24 Binary: binary Encoded Code carrier le css Carrier
-- statement:
--   The Ngu24 Binary construction uses the binary Encoded Code carrier le css Carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L207-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L207-L220

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

theorem QEC.Distillation.Ngu24Binary.binaryEncodedCode_carrier_le_cssCarrier (i : Nat) :
    (binaryEncodedCode i).code.carrier ≤ (binaryCSSCode i).stabilizer.code.carrier := by sorry
