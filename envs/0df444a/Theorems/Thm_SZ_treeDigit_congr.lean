-- Prove2me | Theorems.Thm_SZ_treeDigit_congr
-- name    : SZ.treeDigit_congr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:22:49.293849+00:00
-- url     : https://prove2.me/theorems/173c1d2c-c834-4dcb-87f6-43d2ca0059b8
-- title:
--   SZ: tree Digit congr
-- statement:
--   The SZ construction uses the tree Digit congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1108-L1118
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1108-L1118

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.treeDigit_congr {β β' : ℕ → Bool} {n : ℕ} (hagree : ∀ i, i < n → β i = β' i)
    {k : ℕ} (hle : (node β (k + 1)).used ≤ n) : treeDigit β k = treeDigit β' k := by sorry
