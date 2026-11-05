-- Prove2me | Theorems.Thm_VariableBound_Search_fold_stepD
-- name    : VariableBound.Search.fold_stepD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:40:31.987211+00:00
-- url     : https://prove2.me/theorems/b8ddc759-8069-4f02-9d9c-c807e9f637d3
-- title:
--   Search: fold step D
-- statement:
--   The fold of `stepD` from a pair (l₀, key l₀) ends in a pair (l, key l), where l is l₀ or a
--   member of the list, and key l is at most key l₀ and at most the keys of all members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L120-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L120-L145

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

theorem VariableBound.Search.fold_stepD (key : List ℕ → ℤ) : ∀ (fam : List (List ℕ)) (b : List ℕ × ℤ), b.2 = key b.1 →
    ∃ c, fam.foldl (stepD key) (some b) = some c ∧ c.2 = key c.1 ∧ (c.1 = b.1 ∨ c.1 ∈ fam) ∧ c.2 ≤ b.2 ∧ ∀ l ∈ fam, c.2 ≤ key l := by sorry
