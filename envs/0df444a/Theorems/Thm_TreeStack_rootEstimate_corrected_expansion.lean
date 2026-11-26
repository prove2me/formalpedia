-- Prove2me | Theorems.Thm_TreeStack_rootEstimate_corrected_expansion
-- name    : TreeStack.rootEstimate_corrected_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:06.082087+00:00
-- url     : https://prove2.me/theorems/46a625e3-2c0c-426a-b282-b7a6d72bfb18
-- title:
--   Tree Stack: root Estimate corrected expansion
-- statement:
--   Correct root-sensitive expansion of the rooted estimator.
--   This replaces the false helper identity that drops a degree-one root.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L74-L81
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L74-L81

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.rootEstimate_corrected_expansion {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    rootEstimate T r =
      1 + leafCount T r + T.graph.degree r +
        ∑ v ∈ nonRootInternalVertices T r,
          T.graph.degree v * 2 ^ T.graph.dist r v := by sorry
