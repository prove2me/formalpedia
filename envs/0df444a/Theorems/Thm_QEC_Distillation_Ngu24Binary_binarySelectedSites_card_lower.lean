-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binarySelectedSites_card_lower
-- name    : QEC.Distillation.Ngu24Binary.binarySelectedSites_card_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:13.87753+00:00
-- url     : https://prove2.me/theorems/67d559f4-490c-4924-ba25-91d08b889eee
-- title:
--   Ngu24 Binary: binary Selected Sites card lower
-- statement:
--   The Ngu24 Binary construction uses the binary Selected Sites card lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L85-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L85-L88

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

theorem QEC.Distillation.Ngu24Binary.binarySelectedSites_card_lower :
    Fintype.card J ≤ (binarySelectedSites J).card := by sorry
