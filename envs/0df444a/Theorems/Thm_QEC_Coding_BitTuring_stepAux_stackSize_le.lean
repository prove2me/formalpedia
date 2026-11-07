-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_stepAux_stackSize_le
-- name    : QEC.Coding.BitTuring.stepAux_stackSize_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:51.180619+00:00
-- url     : https://prove2.me/theorems/8f6d40cc-0c87-414b-bec4-033aaf2d1a54
-- title:
--   Bit Turing: step Aux stack Size le
-- statement:
--   Instruction induction bounds growth by the actual push count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L63-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L63-L81

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators

theorem QEC.Coding.BitTuring.stepAux_stackSize_le {K Λ σ : Type} [Fintype K] [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (tapes : K → List Bool) :
    stackSize (TM2.stepAux q v tapes).stk ≤ stackSize tapes + pushes q := by sorry
