-- Prove2me | Theorems.Thm_SZ_node_used_zero
-- name    : SZ.node_used_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:22:13.011271+00:00
-- url     : https://prove2.me/theorems/7b9d4b26-c525-425e-b784-c458055c05b3
-- title:
--   SZ: node used zero
-- statement:
--   The SZ construction uses the node used zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1038-L1038
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1038-L1038

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_used_zero (β : ℕ → Bool) : (node β 0).used = 0 := by sorry
