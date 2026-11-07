-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTripleSupport_card
-- name    : QEC.Distillation.Ngu24Binary.binaryTripleSupport_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:11:56.839191+00:00
-- url     : https://prove2.me/theorems/d3c5b9af-45df-4312-8c68-2549cec66b84
-- title:
--   Ngu24 Binary: binary Triple Support card
-- statement:
--   The Ngu24 Binary construction uses the binary Triple Support card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L55-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L55-L58

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
variable [Fintype J]

theorem QEC.Distillation.Ngu24Binary.binaryTripleSupport_card (x : J × Fin 512) :
    (binaryTripleSupport J x).card = 3 := by sorry
