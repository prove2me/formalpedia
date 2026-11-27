-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxDegreePotential_sub_leafSlack_eq_auxCompactPotential
-- name    : TreeStack.OrientedBranch.auxDegreePotential_sub_leafSlack_eq_auxCompactPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:45.395206+00:00
-- url     : https://prove2.me/theorems/0b219fb0-1a91-51fe-8a05-edcb1d74db53
-- title:
--   Oriented Branch: aux Degree Potential sub leaf Slack eq aux Compact Potential
-- statement:
--   Removing the leaf slack from the degree potential leaves exactly one unit
--   per ambient leaf plus the weighted internal-vertex potential.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L295-L336
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L295-L336

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxDegreePotential_sub_leafSlack_eq_auxCompactPotential
    [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxDegreePotential C ambientRoot hScores -
        auxLeafSlack C ambientRoot hScores =
      auxCompactPotential C ambientRoot hScores := by sorry
