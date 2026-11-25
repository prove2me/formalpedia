-- Prove2me | Theorems.Thm_SZ_node_used_unbounded
-- name    : SZ.node_used_unbounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:23:43.872567+00:00
-- url     : https://prove2.me/theorems/79553b6a-302d-5577-9144-7c0971bede20
-- title:
--   SZ: node used unbounded
-- statement:
--   The SZ construction uses the node used unbounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1057-L1066
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1057-L1066

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_used_unbounded (β : ℕ → Bool) (n : ℕ) : ∃ k, n < (node β k).used := by sorry
