-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrimeLoop_unaryInput_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop.unaryInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:39:50.786201+00:00
-- url     : https://prove2.me/theorems/cc53c608-be64-4303-b9e8-5df68fcbdfeb
-- title:
--   Prime Loop: unary Input injective
-- statement:
--   The Prime Loop construction uses the unary Input injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrimality.lean#L407-L409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrimality.lean#L407-L409

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrimality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop.unaryInput_injective : Function.Injective unaryInput := by sorry
