-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_tripleInput_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.tripleInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:05:18.831377+00:00
-- url     : https://prove2.me/theorems/9c0ad896-fd49-4bd1-b6e2-d4e1975c3ccd
-- title:
--   Factor Test: triple Input injective
-- statement:
--   The unary input encoding distinguishes all natural triples.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTest.lean#L374-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTest.lean#L374-L381

import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.tripleInput_injective :
    Function.Injective (fun x : ℕ × (ℕ × ℕ) => tripleInput x.1 x.2.1 x.2.2) := by sorry
