-- Prove2me | Theorems.Thm_TreeStack_universal_stackable_gt_card
-- name    : TreeStack.universal_stackable_gt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:40.246811+00:00
-- url     : https://prove2.me/theorems/4be0a515-cc55-54ed-b86c-93ecc25e325f
-- title:
--   Tree Stack: universal stackable gt card
-- statement:
--   Audit repair for the exact-size convention: if every configuration of
--   exactly `t` pebbles is stackable and `t ≥ 2`, then `t` strictly exceeds
--   the number of vertices.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L117-L126
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L117-L126

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
set_option autoImplicit false
open TreeStack

theorem TreeStack.universal_stackable_gt_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {t : ℕ} (hU : UniversalStackable G t) (ht : 2 ≤ t) :
    Fintype.card V < t := by sorry
