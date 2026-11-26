-- Prove2me | Theorems.Thm_TranslationCollisionSwitching_certifiedCode_injective
-- name    : TranslationCollisionSwitching.certifiedCode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:16.423811+00:00
-- url     : https://prove2.me/theorems/a24230b5-805d-5574-9b0b-9430de5fbe80
-- title:
--   Translation Collision Switching: certified Code injective
-- statement:
--   The Translation Collision Switching construction uses the certified Code injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3316-L3418
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3316-L3418

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

theorem TranslationCollisionSwitching.certifiedCode_injective {start : OrientedEdge G} {k L : ℕ} :
    Function.Injective
      (certifiedCode (d := d) G hG :
        CertifiedClassifiedReturn (d := d) G hG start k L →
          RotationSystem d V × (Fin L × Offset d)) := by sorry
