-- Prove2me | Theorems.Thm_TranslationCollisionSwitching_high_switching_card_bound
-- name    : TranslationCollisionSwitching.high_switching_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:53.642089+00:00
-- url     : https://prove2.me/theorems/98770290-2189-4195-9cd1-80ab4a37982c
-- title:
--   Translation Collision Switching: high switching card bound
-- statement:
--   The Translation Collision Switching construction uses the high switching card bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3431-L3448
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3431-L3448

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

theorem TranslationCollisionSwitching.high_switching_card_bound (start : OrientedEdge G) (k : ℕ)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k * Nat.card (GoodOmega d G hG start k) ≤
      8 * Nat.card (RotationSystem d V) *
        degreeCutoff d (Fintype.card V) k * (d - 1) := by sorry
