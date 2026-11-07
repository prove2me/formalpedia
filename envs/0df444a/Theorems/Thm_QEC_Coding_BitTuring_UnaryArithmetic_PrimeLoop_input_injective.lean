-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrimeLoop_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:17:54.89322+00:00
-- url     : https://prove2.me/theorems/2ca153f4-ee8d-4ed7-be96-1f31c2110112
-- title:
--   Prime Loop: input injective
-- statement:
--   The Prime Loop construction uses the input injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrimality.lean#L330-L333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrimality.lean#L330-L333

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrimality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop.input_injective : Function.Injective input := by sorry
