-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceFiber_heightDominated_of_nonempty
-- name    : TreeStack.OrientedBranch.auxSourceFiber_heightDominated_of_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:16:53.8638+00:00
-- url     : https://prove2.me/theorems/c95fe2b3-c818-4255-8c5d-e02f7293aecc
-- title:
--   Oriented Branch: aux Source Fiber height Dominated of nonempty
-- statement:
--   Every nonempty canonical source fibre is height-dominated by its own
--   source, in fact with equality pointwise.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L428-L447
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L428-L447

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceFiber_heightDominated_of_nonempty
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V)
    (hNonempty : (auxSourceFiber C ambientRoot hScores r).Nonempty) :
    HeightDominated (T := T)
      (fun v => auxHeight C ambientRoot hScores v)
      (auxSourceFiber C ambientRoot hScores r) r := by sorry
