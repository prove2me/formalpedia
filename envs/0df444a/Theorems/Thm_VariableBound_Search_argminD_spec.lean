-- Prove2me | Theorems.Thm_VariableBound_Search_argminD_spec
-- name    : VariableBound.Search.argminD_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:40:48.611503+00:00
-- url     : https://prove2.me/theorems/a9e147a0-fb9c-4472-9203-3acbfe98f633
-- title:
--   Search: argmin D spec
-- statement:
--   On a list that is not empty, `argminD` returns a member with the smallest key.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L148-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L148-L166

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Search_Correct
set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset

theorem VariableBound.Search.argminD_spec (key : List ℕ → ℤ) (fam : List (List ℕ)) (h : fam ≠ []) : argminD key fam ∈ fam ∧ ∀ l ∈ fam, key (argminD key fam) ≤ key l := by sorry
