-- Prove2me | Theorems.Thm_TreeStack_sigma_corrected_expansion
-- name    : TreeStack.sigma_corrected_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:13.879322+00:00
-- url     : https://prove2.me/theorems/de9de529-96a9-4df0-a5f5-394a051dd587
-- title:
--   Tree Stack: sigma corrected expansion
-- statement:
--   Correct root-sensitive expansion of sigma.  In particular, the root
--   contribution is retained even when the root itself is a leaf.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L60-L70
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L60-L70

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.sigma_corrected_expansion {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    sigma T r =
      1 + T.graph.degree r +
        ∑ v ∈ nonRootInternalVertices T r,
          T.graph.degree v * 2 ^ T.graph.dist r v := by sorry
