-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_boolBits_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.boolBits_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:14:22.198208+00:00
-- url     : https://prove2.me/theorems/61ed2d73-7ca0-49c9-a96e-307c7bdb71b3
-- title:
--   Factor Test: bool Bits injective
-- statement:
--   The singleton output encoding distinguishes both Boolean values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTest.lean#L392-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTest.lean#L392-L394

import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.boolBits_injective : Function.Injective boolBits := by sorry
