-- Prove2me | Theorems.Thm_TranslationOuter_simpleProbability_le_one
-- name    : TranslationOuter.simpleProbability_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:57.485335+00:00
-- url     : https://prove2.me/theorems/c507faec-10a1-4470-960e-751c5fa6be8d
-- title:
--   Translation Outer: simple Probability le one
-- statement:
--   The Translation Outer construction uses the simple Probability le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3980-L3995
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3980-L3995

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

theorem TranslationOuter.simpleProbability_le_one
    {V : Type u} [Fintype V]
    (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
    (start : OrientedEdge G) (k : ℕ) (hk : 0 < k) :
    simpleProbability G start k ≤ 1 := by sorry
