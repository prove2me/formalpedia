-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi2_symm_apply
-- name    : QEC.Distillation.Ngu24Binary.binaryPi2_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:14.381213+00:00
-- url     : https://prove2.me/theorems/87a2cc20-a8b8-45fa-b6f7-d1a1237299a3
-- title:
--   Ngu24 Binary: binary Pi2 symm apply
-- statement:
--   The Ngu24 Binary construction uses the binary Pi2 symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L30-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L30-L31

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

theorem QEC.Distillation.Ngu24Binary.binaryPi2_symm_apply (j : J) (q : Fin 512) :
    (binaryPi2 J).symm (j, q) = (j, f256MFEpi2 q) := by sorry

attribute [defeq] QEC.Distillation.Ngu24Binary.binaryPi2_symm_apply
