-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_tripleInput_dropWhile
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.tripleInput_dropWhile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:05:26.340221+00:00
-- url     : https://prove2.me/theorems/3949ba79-167c-4b3a-be53-09038a20a6dd
-- title:
--   Factor Test: triple Input drop While
-- statement:
--   Recover the remaining pair after reading to the first delimiter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTest.lean#L367-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTest.lean#L367-L371

import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.tripleInput_dropWhile (a b q : ℕ) :
    (tripleInput a b q).dropWhile id = false :: pairInput b q := by sorry
