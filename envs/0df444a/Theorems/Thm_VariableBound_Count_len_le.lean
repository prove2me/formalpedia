-- Prove2me | Theorems.Thm_VariableBound_Count_len_le
-- name    : VariableBound.Count.len_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:49:57.619448+00:00
-- url     : https://prove2.me/theorems/e75ae6ba-dd15-452d-9529-6fc6496c5062
-- title:
--   Count: len le
-- statement:
--   The word of a list of at most R lists of at most s numbers that are at most N has length at most
--   8(R + 1)(s + 1)(size(N) + 2) + 8.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L121-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L121-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset

theorem VariableBound.Count.len_le (R s N : ℕ) (L : List (List ℕ)) (h1 : L.length ≤ R) (h2 : ∀ l ∈ L, l.length ≤ s ∧ ∀ E ∈ l, E ≤ N) :
    len L ≤ 8 * (R + 1) * (s + 1) * (Nat.size N + 2) + 8 := by sorry
