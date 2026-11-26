-- Prove2me | Theorems.Thm_TranslationReversal_classified_reverse_exteriorReturnVertices
-- name    : TranslationReversal.classified_reverse_exteriorReturnVertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:23.814265+00:00
-- url     : https://prove2.me/theorems/9785ecc3-698b-461a-bd0a-def5948b0460
-- title:
--   Translation Reversal: classified reverse exterior Return Vertices
-- statement:
--   The Translation Reversal construction uses the classified reverse exterior Return Vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2393-L2425
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L2393-L2425

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

theorem TranslationReversal.classified_reverse_exteriorReturnVertices (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1)) :
    exteriorReturnVertices (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') =
      exteriorReturnVertices (d := d) G hG start rho k q := by sorry
