-- Prove2me | Theorems.Thm_SZ_node_st_succ
-- name    : SZ.node_st_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:26.930681+00:00
-- url     : https://prove2.me/theorems/f04cb234-dc20-4a43-a224-85f239c276bf
-- title:
--   SZ: node st succ
-- statement:
--   The SZ construction uses the node st succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L636-L639
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L636-L639

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_st_succ (β : ℕ → Bool) (k : ℕ) :
    (node β (k + 1)).st = stepS (node β k).st (treeDigit β k) := by sorry
