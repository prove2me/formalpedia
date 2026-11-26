-- Prove2me | Theorems.Thm_TranslationCollisionSwitching_returnEndpoint_congr
-- name    : TranslationCollisionSwitching.returnEndpoint_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:10.407102+00:00
-- url     : https://prove2.me/theorems/9de8cca7-b769-42cb-9752-c87d1a0f4c6d
-- title:
--   Translation Collision Switching: return Endpoint congr
-- statement:
--   The Translation Collision Switching construction uses the return Endpoint congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3297-L3307
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3297-L3307

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
open TranslationCollisionSwitching
open TranslationReversal TranslationIntegration
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationCollisionSwitching.graphAdjDecidable
attribute [local instance] TranslationCollisionSwitching.vertexDecidableEq

theorem TranslationCollisionSwitching.returnEndpoint_congr (start : OrientedEdge G)
    {rho sigma : RotationSystem d V} {k : ℕ}
    {q r : DeviationIndex d k}
    (hrho : rho = sigma) (hqr : q = r)
    (hq : IsValidDeviation d G hG start rho q)
    (hr : IsValidDeviation d G hG start sigma r) :
    returnEndpoint d G hG start rho k ⟨q, hq⟩ =
      returnEndpoint d G hG start sigma k ⟨r, hr⟩ := by sorry
