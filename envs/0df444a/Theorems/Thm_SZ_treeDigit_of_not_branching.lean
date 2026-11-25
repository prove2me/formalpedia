-- Prove2me | Theorems.Thm_SZ_treeDigit_of_not_branching
-- name    : SZ.treeDigit_of_not_branching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:37:23.721802+00:00
-- url     : https://prove2.me/theorems/2fc7aa32-09bd-4465-91fb-c6f621ef157b
-- title:
--   SZ: tree Digit of not branching
-- statement:
--   The SZ construction uses the tree Digit of not branching property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L684-L686
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L684-L686

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.treeDigit_of_not_branching (β : ℕ → Bool) {k : ℕ} (h : ¬ Branching (node β k)) :
    treeDigit β k = pick (valS (node β k).st) := by sorry
