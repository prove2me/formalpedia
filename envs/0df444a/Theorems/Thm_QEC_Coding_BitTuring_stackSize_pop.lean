-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_stackSize_pop
-- name    : QEC.Coding.BitTuring.stackSize_pop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:42.495202+00:00
-- url     : https://prove2.me/theorems/64f3f9c1-c10f-41a6-8894-392a586aac89
-- title:
--   Bit Turing: stack Size pop
-- statement:
--   One pop cannot increase total stack length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L55-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L55-L60

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators

theorem QEC.Coding.BitTuring.stackSize_pop {K : Type} [Fintype K] [DecidableEq K]
    (tapes : K → List Bool) (k : K) :
    stackSize (Function.update tapes k (tapes k).tail) ≤ stackSize tapes := by sorry
