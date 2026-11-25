-- Prove2me | Theorems.Thm_SZ_node_g2_succ
-- name    : SZ.node_g2_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:20:32.084291+00:00
-- url     : https://prove2.me/theorems/52674692-ab7c-4222-97a8-ed6d9c5a70c9
-- title:
--   SZ: node g2 succ
-- statement:
--   The SZ construction uses the node g2 succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L717-L724
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L717-L724

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_g2_succ (β : ℕ → Bool) (k : ℕ) :
    (node β (k + 1)).g2 = true → (node β k).g2 = true ∨ (treeDigit β k).2 = 2 := by sorry
