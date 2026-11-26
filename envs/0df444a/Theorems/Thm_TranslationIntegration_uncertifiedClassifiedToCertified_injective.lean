-- Prove2me | Theorems.Thm_TranslationIntegration_uncertifiedClassifiedToCertified_injective
-- name    : TranslationIntegration.uncertifiedClassifiedToCertified_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:01.716119+00:00
-- url     : https://prove2.me/theorems/e148baed-08c2-41bb-a755-dbe4f5f1554d
-- title:
--   Translation Integration: uncertified Classified To Certified injective
-- statement:
--   The Translation Integration construction uses the uncertified Classified To Certified injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2864-L2872
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2864-L2872

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

theorem TranslationIntegration.uncertifiedClassifiedToCertified_injective
    {start : OrientedEdge G} {k L : ℕ} :
    Function.Injective
      (uncertifiedClassifiedToCertified (d := d) G hG :
        UncertifiedClassifiedReturn (d := d) G hG start k L →
          CertifiedClassifiedReturn (d := d) G hG start k L) := by sorry
