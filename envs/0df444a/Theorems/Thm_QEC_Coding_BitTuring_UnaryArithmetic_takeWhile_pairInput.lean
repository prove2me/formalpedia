-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_takeWhile_pairInput
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.takeWhile_pairInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:04:33.772368+00:00
-- url     : https://prove2.me/theorems/b55880fb-3a85-4b06-a072-3f1bbba13690
-- title:
--   Unary Arithmetic: take While pair Input
-- statement:
--   The true prefix decodes exactly the first unary operand.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L167-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L167-L170

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.takeWhile_pairInput (a b : ℕ) : (pairInput a b).takeWhile id = unary a := by sorry
