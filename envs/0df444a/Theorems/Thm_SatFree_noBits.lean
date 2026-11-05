-- Prove2me | Theorems.Thm_SatFree_noBits
-- name    : SatFree.noBits
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:48:26.318506+00:00
-- url     : https://prove2.me/theorems/81e11422-5dfe-476c-bf8b-55c452b52560
-- title:
--   Sat Free: no Bits
-- statement:
--   With no random bits the input is the code alone: if M halts on the word x with the bit b within
--   t steps, it does so for every string of no bits behind x, and the number of such strings, 1, is at
--   least (1 − 0)·2^0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Random.lean#L32-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Random.lean#L32-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Random
set_option autoImplicit false
section
section
open SatFree
open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal

theorem SatFree.noBits (M : TM2ComputableAux Bool Bool) (x : List Bool) (b : Bool) (t : ℕ)
    (ev : Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)) :
    (∀ w : Fin 0 → Bool, ∃ b : Bool, Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)) ∧
    (1 - (0 : ℝ)) * (2 : ℝ) ^ 0 ≤ (Nat.card {w : Fin 0 → Bool //
      Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)} : ℝ) := by sorry
