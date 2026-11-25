-- Prove2me | Theorems.Thm_SZ_tree_isRun
-- name    : SZ.tree_isRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:01:10.975902+00:00
-- url     : https://prove2.me/theorems/acc040a5-27ec-45a3-a450-c70ca4f5f1e9
-- title:
--   SZ: tree is Run
-- statement:
--   The SZ construction uses the tree is Run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L669-L672
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L669-L672

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.tree_isRun (β : ℕ → Bool) : IsRun (-12, 9) (treeDigit β) := by sorry
