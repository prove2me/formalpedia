-- Prove2me | Theorems.Thm_TranslationIntegration_countedEligible_lower
-- name    : TranslationIntegration.countedEligible_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:36.405141+00:00
-- url     : https://prove2.me/theorems/7f7babb3-1645-583f-8460-d66b3bed3850
-- title:
--   Translation Integration: counted Eligible lower
-- statement:
--   Sum the pointwise `k/4` estimate over all good plans.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2731-L2751
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2731-L2751

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
open TranslationIntegration
open TranslationReversal
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationIntegration.graphAdjDecidable
attribute [local instance] TranslationIntegration.vertexDecidableEq

theorem TranslationIntegration.countedEligible_lower (start : OrientedEdge G) (k : ℕ)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k * Nat.card (GoodOmega d G hG start k) ≤
      4 * Nat.card (CountedEligibleReturn (d := d) G hG start k) := by sorry
