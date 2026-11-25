-- Prove2me | Theorems.Thm_SZ_node_used_succ_branch
-- name    : SZ.node_used_succ_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:52:56.653127+00:00
-- url     : https://prove2.me/theorems/15cb47d7-426a-490b-94de-fd8d4ee018ac
-- title:
--   SZ: node used succ branch
-- statement:
--   The SZ construction uses the node used succ branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1040-L1042
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1040-L1042

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_used_succ_branch (β : ℕ → Bool) {k : ℕ} (h : Branching (node β k)) :
    (node β (k + 1)).used = (node β k).used + 1 := by sorry
