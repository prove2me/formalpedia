-- Prove2me | Theorems.Thm_TranslationReversal_reversedReturn_pathIncomingDarts
-- name    : TranslationReversal.reversedReturn_pathIncomingDarts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:07:40.371397+00:00
-- url     : https://prove2.me/theorems/d0ed5252-5093-458a-8d8a-98a89fea32be
-- title:
--   Translation Reversal: reversed Return path Incoming Darts
-- statement:
--   The Translation Reversal construction uses the reversed Return path Incoming Darts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2067-L2077
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2067-L2077

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
open TranslationReversal
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationReversal.graphAdjDecidable
attribute [local instance] TranslationReversal.vertexDecidableEq

theorem TranslationReversal.reversedReturn_pathIncomingDarts (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) :
    pathIncomingDarts d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k =
      pathIncomingDarts d G hG start rho k := by sorry
