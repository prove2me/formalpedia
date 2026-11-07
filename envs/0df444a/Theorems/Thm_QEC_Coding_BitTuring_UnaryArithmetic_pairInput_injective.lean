-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_pairInput_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.pairInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:03:58.084024+00:00
-- url     : https://prove2.me/theorems/6ce95e57-de60-4fdf-bc90-ec3f7359dd44
-- title:
--   Unary Arithmetic: pair Input injective
-- statement:
--   The delimiter input encoding never identifies different natural pairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L179-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L179-L185

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.pairInput_injective : Function.Injective (fun x : ℕ × ℕ => pairInput x.1 x.2) := by sorry
