-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_mass_le_auxDegreePotential_sub_leafSlack
-- name    : TreeStack.OrientedBranch.mass_le_auxDegreePotential_sub_leafSlack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:11.764966+00:00
-- url     : https://prove2.me/theorems/1eb505b3-f45c-5cb0-9c64-fdd7bd3d8ca1
-- title:
--   Oriented Branch: mass le aux Degree Potential sub leaf Slack
-- statement:
--   Ordinary mass is bounded by the weighted degree potential after removing
--   the leaf-weight slack.  This is the ambient-tree leaf-slack conversion and
--   does not require transporting the configuration to a support subtype.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L174-L190
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L174-L190

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.mass_le_auxDegreePotential_sub_leafSlack
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (mass C : ℤ) ≤
      auxDegreePotential C ambientRoot hScores -
        auxLeafSlack C ambientRoot hScores := by sorry
