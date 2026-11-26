-- Prove2me | Theorems.Thm_TranslationReversal_reverseSimpleClassifiedReturn_involutive
-- name    : TranslationReversal.reverseSimpleClassifiedReturn_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:27.152106+00:00
-- url     : https://prove2.me/theorems/75bac16f-95cd-5ba3-a04d-f3d60ee87f4d
-- title:
--   Translation Reversal: reverse Simple Classified Return involutive
-- statement:
--   The Translation Reversal construction uses the reverse Simple Classified Return involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2492-L2502
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2492-L2502

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

theorem TranslationReversal.reverseSimpleClassifiedReturn_involutive
    {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) :
    reverseSimpleClassifiedReturn (d := d) G hG
        (reverseSimpleClassifiedReturn (d := d) G hG q) = q := by sorry
