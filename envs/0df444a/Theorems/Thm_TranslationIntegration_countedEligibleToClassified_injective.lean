-- Prove2me | Theorems.Thm_TranslationIntegration_countedEligibleToClassified_injective
-- name    : TranslationIntegration.countedEligibleToClassified_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:34.451076+00:00
-- url     : https://prove2.me/theorems/f6cee92e-1d89-58da-a453-349c690b25b7
-- title:
--   Translation Integration: counted Eligible To Classified injective
-- statement:
--   The Translation Integration construction uses the counted Eligible To Classified injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2716-L2728
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2716-L2728

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

theorem TranslationIntegration.countedEligibleToClassified_injective (start : OrientedEdge G) (k : ℕ) :
    Function.Injective (countedEligibleToClassified (d := d) G hG start k) := by sorry
