-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_dropWhile_pairInput
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.dropWhile_pairInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:04:20.573495+00:00
-- url     : https://prove2.me/theorems/c465a2b5-6d38-4c16-ae8b-bea0543a701c
-- title:
--   Unary Arithmetic: drop While pair Input
-- statement:
--   Removing the true prefix exposes exactly the delimiter and second operand.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L173-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L173-L176

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.dropWhile_pairInput (a b : ℕ) : (pairInput a b).dropWhile id = false :: unary b := by sorry
