-- Prove2me | Theorems.Thm_TranslationReversal_reversedReturn_returnBase
-- name    : TranslationReversal.reversedReturn_returnBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:07:55.001368+00:00
-- url     : https://prove2.me/theorems/ce7f1bcf-51a6-49b3-b465-f31351f44cc4
-- title:
--   Translation Reversal: reversed Return return Base
-- statement:
--   The Translation Reversal construction uses the reversed Return return Base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2142-L2165
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2142-L2165

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

theorem TranslationReversal.reversedReturn_returnBase (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k)
    (a : DeviationIndex d k) :
    returnBase d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) a =
      returnBase d G hG start rho a := by sorry
