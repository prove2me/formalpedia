-- Prove2me | Theorems.Thm_VariableBound_Count_len_row
-- name    : VariableBound.Count.len_row
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:49:16.525522+00:00
-- url     : https://prove2.me/theorems/4d05f0ad-1522-4725-8714-fb748a6ca89d
-- title:
--   Count: len row
-- statement:
--   The word of a list l of numbers that are at most N has length at most |l|·(3·size(N) + 4) + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L100-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L100-L107

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

theorem VariableBound.Count.len_row (N : ℕ) (l : List ℕ) (h : ∀ E ∈ l, E ≤ N) : len l ≤ l.length * (3 * Nat.size N + 4) + 2 := by sorry
