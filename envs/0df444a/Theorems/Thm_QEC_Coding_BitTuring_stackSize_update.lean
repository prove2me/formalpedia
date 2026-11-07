-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_stackSize_update
-- name    : QEC.Coding.BitTuring.stackSize_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:56.152953+00:00
-- url     : https://prove2.me/theorems/41497b69-869b-4369-8cb4-c16eb5fa88e2
-- title:
--   Bit Turing: stack Size update
-- statement:
--   Exact length balance when replacing one stack.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L32-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L32-L44

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators

theorem QEC.Coding.BitTuring.stackSize_update {K : Type} [Fintype K] [DecidableEq K]
    (tapes : K → List Bool) (k : K) (value : List Bool) :
    stackSize (Function.update tapes k value) + (tapes k).length =
      stackSize tapes + value.length := by sorry
