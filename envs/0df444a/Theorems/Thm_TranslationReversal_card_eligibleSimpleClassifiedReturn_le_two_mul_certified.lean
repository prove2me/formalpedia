-- Prove2me | Theorems.Thm_TranslationReversal_card_eligibleSimpleClassifiedReturn_le_two_mul_certified
-- name    : TranslationReversal.card_eligibleSimpleClassifiedReturn_le_two_mul_certified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:12.538686+00:00
-- url     : https://prove2.me/theorems/b5ead8c5-3be1-5107-a765-90c3842b4f2e
-- title:
--   Translation Reversal: card eligible Simple Classified Return le two mul certified
-- statement:
--   At least half of all eligible simple classified returns are certified.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2626-L2637
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2626-L2637

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

theorem TranslationReversal.card_eligibleSimpleClassifiedReturn_le_two_mul_certified
    {start : OrientedEdge G} {k L : ℕ} :
    Nat.card (EligibleSimpleClassifiedReturn (d := d) G hG start k L) ≤
      2 * Nat.card
        (CertifiedEligibleSimpleReturn (d := d) G hG start k L) := by sorry
