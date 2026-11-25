-- Prove2me | Theorems.Thm_SZ_treeDigit_of_branching
-- name    : SZ.treeDigit_of_branching
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:18:32.533352+00:00
-- url     : https://prove2.me/theorems/dbb2fd82-3fd6-4785-a2b0-e5c6d3ac532b
-- title:
--   SZ: tree Digit of branching
-- statement:
--   The SZ construction uses the tree Digit of branching property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L688-L690
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L688-L690

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.treeDigit_of_branching (β : ℕ → Bool) {k : ℕ} (h : Branching (node β k)) :
    treeDigit β k = branchDigit (valS (node β k).st) (β (node β k).used) := by sorry
