-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTrial_recordInput_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial.recordInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:16:17.902579+00:00
-- url     : https://prove2.me/theorems/378e784a-c931-4a54-a226-7d30a9910605
-- title:
--   Factor Trial: record Input injective
-- statement:
--   The Factor Trial construction uses the record Input injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTrial.lean#L604-L606
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTrial.lean#L604-L606

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial.recordInput_injective : Function.Injective recordInput := by sorry
