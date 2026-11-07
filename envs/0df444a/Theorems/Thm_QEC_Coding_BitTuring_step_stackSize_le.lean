-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_step_stackSize_le
-- name    : QEC.Coding.BitTuring.step_stackSize_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:54:00.83736+00:00
-- url     : https://prove2.me/theorems/db18cd2e-deee-484e-b67d-2a19c98fe03a
-- title:
--   Bit Turing: step stack Size le
-- statement:
--   One actual machine transition satisfies the syntactic growth bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L95-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L95-L106

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators

theorem QEC.Coding.BitTuring.step_stackSize_le {K Λ σ : Type} [Fintype K] [DecidableEq K] [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (c c' : TM2.Cfg (fun _ : K => Bool) Λ σ) (hstep : TM2.step M c = some c') :
    stackSize c'.stk ≤ stackSize c.stk + programPushes M := by sorry
