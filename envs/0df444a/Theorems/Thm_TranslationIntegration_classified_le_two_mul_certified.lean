-- Prove2me | Theorems.Thm_TranslationIntegration_classified_le_two_mul_certified
-- name    : TranslationIntegration.classified_le_two_mul_certified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:51.839741+00:00
-- url     : https://prove2.me/theorems/582ee70c-0aa9-5361-8aea-731bd93f7bc6
-- title:
--   Translation Integration: classified le two mul certified
-- statement:
--   Excursion reversal certifies at least half of all classified returns.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2879-L2893
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2879-L2893

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

theorem TranslationIntegration.classified_le_two_mul_certified
    (start : OrientedEdge G) (k L : ℕ) :
    Nat.card (ClassifiedEligibleReturn (d := d) G hG start k L) ≤
      2 * Nat.card (CertifiedClassifiedReturn (d := d) G hG start k L) := by sorry
