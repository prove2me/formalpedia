-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi3_symm_apply
-- name    : QEC.Distillation.Ngu24Binary.binaryPi3_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:24.722635+00:00
-- url     : https://prove2.me/theorems/b5aec495-d5d9-4ef4-a463-3bd65ba53e84
-- title:
--   Ngu24 Binary: binary Pi3 symm apply
-- statement:
--   The Ngu24 Binary construction uses the binary Pi3 symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L33-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L33-L34

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding
open scoped BigOperators
universe u
variable (J : Type u)

theorem QEC.Distillation.Ngu24Binary.binaryPi3_symm_apply (j : J) (q : Fin 512) :
    (binaryPi3 J).symm (j, q) = (j, f256MFEpi3 q) := by sorry

attribute [defeq] QEC.Distillation.Ngu24Binary.binaryPi3_symm_apply
