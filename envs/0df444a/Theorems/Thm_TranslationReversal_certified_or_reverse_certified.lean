-- Prove2me | Theorems.Thm_TranslationReversal_certified_or_reverse_certified
-- name    : TranslationReversal.certified_or_reverse_certified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:09.716407+00:00
-- url     : https://prove2.me/theorems/81c1cbe1-d0c6-5bab-ad2e-95b1b1121fba
-- title:
--   Translation Reversal: certified or reverse certified
-- statement:
--   The Translation Reversal construction uses the certified or reverse certified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2540-L2546
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2540-L2546

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

theorem TranslationReversal.certified_or_reverse_certified
    {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) :
    SimpleReturnCertified (d := d) G hG q ∨
      SimpleReturnCertified (d := d) G hG
        (reverseSimpleClassifiedReturn (d := d) G hG q) := by sorry
