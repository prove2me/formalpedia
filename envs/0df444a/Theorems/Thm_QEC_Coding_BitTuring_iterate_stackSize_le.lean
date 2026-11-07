-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_iterate_stackSize_le
-- name    : QEC.Coding.BitTuring.iterate_stackSize_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:54:03.046647+00:00
-- url     : https://prove2.me/theorems/d6752ebc-1cb8-4919-a78e-916daa910c14
-- title:
--   Bit Turing: iterate stack Size le
-- statement:
--   Counted actual executions satisfy the accumulated stack-growth bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L109-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L109-L135

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators

theorem QEC.Coding.BitTuring.iterate_stackSize_le {K Λ σ : Type} [Fintype K] [DecidableEq K] [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (n : ℕ)
    (c c' : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (hRun : (fun x => x.bind (TM2.step M))^[n] (some c) = some c') :
    stackSize c'.stk ≤ stackSize c.stk + n * programPushes M := by sorry
