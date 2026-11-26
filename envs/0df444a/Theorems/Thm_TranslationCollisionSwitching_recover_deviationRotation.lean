-- Prove2me | Theorems.Thm_TranslationCollisionSwitching_recover_deviationRotation
-- name    : TranslationCollisionSwitching.recover_deviationRotation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:03.831817+00:00
-- url     : https://prove2.me/theorems/6375a204-3e09-5bff-bfd1-ba45e6297ca2
-- title:
--   Translation Collision Switching: recover deviation Rotation
-- statement:
--   The Translation Collision Switching construction uses the recover deviation Rotation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3274-L3288
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3274-L3288

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

theorem TranslationCollisionSwitching.recover_deviationRotation (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) :
    recoverRotation (d := d) G hG start
        (deviationRotation d G hG start rho.1 q.1) q.1.1
        (currentOffset d G hG start rho.1 q.1.1) = rho.1 := by sorry
