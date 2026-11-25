-- Prove2me | Theorems.Thm_SZ_tree_exists_fst_eq_zero
-- name    : SZ.tree_exists_fst_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:19:22.056278+00:00
-- url     : https://prove2.me/theorems/cc848ce8-11fa-5181-8710-184e506a21dc
-- title:
--   SZ: tree exists fst eq zero
-- statement:
--   Between two branchings an `a = 0` is emitted: the flag is reset at the first and set at
--   the second.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L805-L817
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L805-L817

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.tree_exists_fst_eq_zero (β : ℕ → Bool) (N : ℕ) :
    ∃ k, N ≤ k ∧ (treeDigit β k).1 = 0 := by sorry
