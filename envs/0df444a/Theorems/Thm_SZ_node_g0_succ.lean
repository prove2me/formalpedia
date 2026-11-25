-- Prove2me | Theorems.Thm_SZ_node_g0_succ
-- name    : SZ.node_g0_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:28.750165+00:00
-- url     : https://prove2.me/theorems/070afe41-bcd8-5877-9295-416ee5d38561
-- title:
--   SZ: node g0 succ
-- statement:
--   The SZ construction uses the node g0 succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L708-L715
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L708-L715

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_g0_succ (β : ℕ → Bool) (k : ℕ) :
    (node β (k + 1)).g0 = true → (node β k).g0 = true ∨ (treeDigit β k).1 = 0 := by sorry
