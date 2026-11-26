-- Prove2me | Theorems.Thm_TranslationOuter_quantitative_bound_of_high_good_plan_card_bound
-- name    : TranslationOuter.quantitative_bound_of_high_good_plan_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:48.374263+00:00
-- url     : https://prove2.me/theorems/f6eeb10c-0a2b-5608-84da-0ea023cff027
-- title:
--   Translation Outer: quantitative bound of high good plan card bound
-- statement:
--   The switching estimate implies the uniform quantitative probability bound.
--   This theorem includes the pigeonhole case `card V ≤ k` and the low/high
--   regime split.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L4047-L4085
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L4047-L4085

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

theorem TranslationOuter.quantitative_bound_of_high_good_plan_card_bound
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
            Nat.card (RotationSystem d V)) :
    ∀ {V : Type u} [Fintype V]
        (G : SimpleGraph V), IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G), 0 < k →
          simpleProbability G start k ≤
            (K d : ℝ) * (Fintype.card V : ℝ) / (k : ℝ) ^ 2 := by sorry
