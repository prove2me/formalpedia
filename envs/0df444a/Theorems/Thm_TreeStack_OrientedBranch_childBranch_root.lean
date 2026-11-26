-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
-- name    : TreeStack.OrientedBranch.childBranch_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:08:46.862798+00:00
-- url     : https://prove2.me/theorems/80d80ed9-57fd-5c1e-9f2f-6b2faf68f03c
-- title:
--   Oriented Branch: child Branch root
-- statement:
--   The Oriented Branch construction uses the child Branch root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L111-L112
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L111-L112

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.childBranch_root (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).root = c.vertex := by sorry

attribute [defeq] TreeStack.OrientedBranch.childBranch_root
