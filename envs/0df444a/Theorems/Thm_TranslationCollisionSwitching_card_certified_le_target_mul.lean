-- Prove2me | Theorems.Thm_TranslationCollisionSwitching_card_certified_le_target_mul
-- name    : TranslationCollisionSwitching.card_certified_le_target_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:33.370505+00:00
-- url     : https://prove2.me/theorems/02d184af-90de-46c9-ad65-69bafa6e31f7
-- title:
--   Translation Collision Switching: card certified le target mul
-- statement:
--   The Translation Collision Switching construction uses the card certified le target mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3420-L3429
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3420-L3429

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

theorem TranslationCollisionSwitching.card_certified_le_target_mul {start : OrientedEdge G} {k L : ℕ} :
    Nat.card (CertifiedClassifiedReturn (d := d) G hG start k L) ≤
      Nat.card (RotationSystem d V) * L * (d - 1) := by sorry
