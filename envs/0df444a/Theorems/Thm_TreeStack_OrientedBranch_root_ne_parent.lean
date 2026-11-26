-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
-- name    : TreeStack.OrientedBranch.root_ne_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:08:25.261139+00:00
-- url     : https://prove2.me/theorems/f4b9911c-7c6b-4210-b9d8-56a9a1d9d1b7
-- title:
--   Oriented Branch: root ne parent
-- statement:
--   The Oriented Branch construction uses the root ne parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L35-L37
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L35-L37

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.root_ne_parent (B : OrientedBranch T) :
    B.root ≠ B.parent := by sorry
