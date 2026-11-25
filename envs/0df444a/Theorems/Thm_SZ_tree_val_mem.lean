-- Prove2me | Theorems.Thm_SZ_tree_val_mem
-- name    : SZ.tree_val_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:37:15.451889+00:00
-- url     : https://prove2.me/theorems/fa113bd4-445d-4c07-aff4-3711d2a32e76
-- title:
--   SZ: tree val mem
-- statement:
--   The SZ construction uses the tree val mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L657-L667
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L657-L667

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.tree_val_mem (β : ℕ → Bool) (k : ℕ) :
    0 ≤ valS (node β k).st ∧ valS (node β k).st ≤ 3 + 3 * Real.sqrt 3 := by sorry
