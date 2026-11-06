-- Prove2me | Theorems.Thm_VariableBound_Count_len_rows
-- name    : VariableBound.Count.len_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:49:57.225012+00:00
-- url     : https://prove2.me/theorems/acf772ba-bf10-4f64-822f-cf50d8af8c2c
-- title:
--   Count: len rows
-- statement:
--   The word of a list L of lists whose words have length at most c has length at most |L|·(c + 2) + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L110-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L110-L117

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

theorem VariableBound.Count.len_rows (c : ℕ) (L : List (List ℕ)) (h : ∀ l ∈ L, len l ≤ c) : len L ≤ L.length * (c + 2) + 2 := by sorry
