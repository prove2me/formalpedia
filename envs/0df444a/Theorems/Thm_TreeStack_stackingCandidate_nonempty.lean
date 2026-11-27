-- Prove2me | Theorems.Thm_TreeStack_stackingCandidate_nonempty
-- name    : TreeStack.stackingCandidate_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:32.266574+00:00
-- url     : https://prove2.me/theorems/2fdaac02-4f50-4f56-a2d8-fc83e0776976
-- title:
--   Tree Stack: stacking Candidate nonempty
-- statement:
--   The exact-size candidate set is nonempty for every nontrivial finite
--   tree.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L51-L54
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L51-L54

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.stackingCandidate_nonempty
    [Nontrivial V] (T : FiniteTree V) :
    Set.Nonempty {t : ℕ | StackingCandidate T t} := by sorry
