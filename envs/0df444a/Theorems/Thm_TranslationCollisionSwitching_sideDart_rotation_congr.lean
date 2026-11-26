-- Prove2me | Theorems.Thm_TranslationCollisionSwitching_sideDart_rotation_congr
-- name    : TranslationCollisionSwitching.sideDart_rotation_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:13.047493+00:00
-- url     : https://prove2.me/theorems/54e6636b-7d2c-5c36-8803-e9d29d97cb51
-- title:
--   Translation Collision Switching: side Dart rotation congr
-- statement:
--   The Translation Collision Switching construction uses the side Dart rotation congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3309-L3314
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3309-L3314

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
open TranslationCollisionSwitching
open TranslationReversal TranslationIntegration
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationCollisionSwitching.graphAdjDecidable
attribute [local instance] TranslationCollisionSwitching.vertexDecidableEq

theorem TranslationCollisionSwitching.sideDart_rotation_congr (start : OrientedEdge G)
    {rho sigma : RotationSystem d V} {k : ℕ}
    (hrho : rho = sigma) (q : DeviationIndex d k) :
    sideDart d G hG start rho q = sideDart d G hG start sigma q := by sorry
