-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_internal
-- name    : TreeStack.OrientedBranch.obstructionHeight_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:46:05.680232+00:00
-- url     : https://prove2.me/theorems/9b75c9df-4c43-4dd2-808f-c004a65055ee
-- title:
--   Oriented Branch: obstruction Height internal
-- statement:
--   The Oriented Branch construction uses the obstruction Height internal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L116-L130
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L116-L130

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.obstructionHeight_internal (B : OrientedBranch T)
    (hInternal : 1 < T.graph.degree B.root) :
    obstructionHeight B =
      3 + 2 *
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            obstructionHeight
              (B.childBranch
                { vertex := v
                  adj := h.1
                  ne_parent := h.2 })
          else
            0 := by sorry
