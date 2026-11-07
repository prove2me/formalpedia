-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.unary_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:03:52.378495+00:00
-- url     : https://prove2.me/theorems/e13fb8b5-6c81-4c06-bd3d-e9c431bb181a
-- title:
--   Unary Arithmetic: unary injective
-- statement:
--   Unary output encoding never identifies different natural values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L162-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L162-L164

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.unary_injective : Function.Injective unary := by sorry
