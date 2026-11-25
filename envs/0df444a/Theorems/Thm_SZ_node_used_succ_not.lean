-- Prove2me | Theorems.Thm_SZ_node_used_succ_not
-- name    : SZ.node_used_succ_not
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:38:48.197345+00:00
-- url     : https://prove2.me/theorems/c625f48b-039f-439a-aa1e-d1d5ef04c294
-- title:
--   SZ: node used succ not
-- statement:
--   The SZ construction uses the node used succ not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1044-L1046
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1044-L1046

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_used_succ_not (β : ℕ → Bool) {k : ℕ} (h : ¬ Branching (node β k)) :
    (node β (k + 1)).used = (node β k).used := by sorry
