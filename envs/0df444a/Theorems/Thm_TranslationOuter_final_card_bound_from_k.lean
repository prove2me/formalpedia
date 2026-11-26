-- Prove2me | Theorems.Thm_TranslationOuter_final_card_bound_from_k
-- name    : TranslationOuter.final_card_bound_from_k
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:44.100349+00:00
-- url     : https://prove2.me/theorems/8c477f58-7073-5eb8-9b77-6f8f3428ea94
-- title:
--   Translation Outer: final card bound from k
-- statement:
--   The final integral estimate when the double count directly controls
--   `k * good`; this is the form supplied by the generalized eligible-set bound.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3999-L4021
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3999-L4021

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
open TranslationOuter
open GeneralFinalRatio
noncomputable section
universe u

theorem TranslationOuter.final_card_bound_from_k
    (d n k good plans : ℕ) (hd : 3 ≤ d) (hkn : k < n)
    (hinc : k * good ≤
      8 * (d - 1) * cutoff d n k * plans) :
    good * k ^ 2 ≤ K d * n * plans := by sorry
