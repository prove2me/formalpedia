-- Prove2me | Theorems.Thm_TreeStack_sigmaVertices_eq_insert
-- name    : TreeStack.sigmaVertices_eq_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:05:56.415295+00:00
-- url     : https://prove2.me/theorems/b59841c0-3cf9-4685-a116-98146e1a8a4c
-- title:
--   Tree Stack: sigma Vertices eq insert
-- statement:
--   Split the sigma support into the root and the non-root internal vertices.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L50-L56
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L50-L56

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.sigmaVertices_eq_insert {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    sigmaVertices T r = insert r (nonRootInternalVertices T r) := by sorry
