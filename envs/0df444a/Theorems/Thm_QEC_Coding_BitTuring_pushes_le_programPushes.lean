-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_pushes_le_programPushes
-- name    : QEC.Coding.BitTuring.pushes_le_programPushes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:51.550892+00:00
-- url     : https://prove2.me/theorems/666b9b3c-cbe8-433f-8a0c-caad6d8f0e59
-- title:
--   Bit Turing: pushes le program Pushes
-- statement:
--   Every instruction tree is bounded by the finite program maximum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L89-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/StackGrowth.lean#L89-L92

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators

theorem QEC.Coding.BitTuring.pushes_le_programPushes {K Λ σ : Type} [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (l : Λ) :
    pushes (M l) ≤ programPushes M := by sorry
