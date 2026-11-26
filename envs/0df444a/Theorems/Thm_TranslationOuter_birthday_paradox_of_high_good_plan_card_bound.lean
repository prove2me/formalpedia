-- Prove2me | Theorems.Thm_TranslationOuter_birthday_paradox_of_high_good_plan_card_bound
-- name    : TranslationOuter.birthday_paradox_of_high_good_plan_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:57.200817+00:00
-- url     : https://prove2.me/theorems/0c16f614-0e7f-4a14-8847-0447e1ec3aff
-- title:
--   Translation Outer: birthday paradox of high good plan card bound
-- statement:
--   The exact quantifier statement of `birthday_paradox`, conditional only on the
--   high-regime switching-cardinality lemma above.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L4093-L4128
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L4093-L4128

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

theorem TranslationOuter.birthday_paradox_of_high_good_plan_card_bound
    (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (hcard :
      ∀ {V : Type u} [Fintype V]
          (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
          (k : ℕ) (start : OrientedEdge G),
        0 < k →
        k < Fintype.card V →
        K d * Fintype.card V ≤ k ^ 2 →
        k * Nat.card (GoodOmega d G hG start k) ≤
          8 * (d - 1) * cutoff d (Fintype.card V) k *
            Nat.card (RotationSystem d V))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G),
          C * Real.sqrt (Fintype.card V : ℝ) < (k : ℝ) →
            simpleProbability G start k < ε := by sorry
