-- Prove2me | Theorems.Thm_TranslationOuter_simpleWalkCount_le_walkCount
-- name    : TranslationOuter.simpleWalkCount_le_walkCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:27.107832+00:00
-- url     : https://prove2.me/theorems/217d8632-9ac1-5dc4-bd15-ae3441939e5c
-- title:
--   Translation Outer: simple Walk Count le walk Count
-- statement:
--   The Translation Outer construction uses the simple Walk Count le walk Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3963-L3968
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3963-L3968

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

theorem TranslationOuter.simpleWalkCount_le_walkCount
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (start : OrientedEdge G) (k : ℕ) :
    simpleWalkCount G start k ≤ walkCount G start k := by sorry
