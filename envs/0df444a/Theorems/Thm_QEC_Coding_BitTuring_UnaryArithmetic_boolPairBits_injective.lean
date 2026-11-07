-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_boolPairBits_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.boolPairBits_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:04:35.145082+00:00
-- url     : https://prove2.me/theorems/c07323bf-1cc5-4464-b1ba-d7f5f9dd2995
-- title:
--   Unary Arithmetic: bool Pair Bits injective
-- statement:
--   The output encoding distinguishes all Boolean pairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryComparison.lean#L321-L324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryComparison.lean#L321-L324

import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.boolPairBits_injective : Function.Injective boolPairBits := by sorry
