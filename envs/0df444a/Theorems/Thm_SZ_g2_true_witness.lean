-- Prove2me | Theorems.Thm_SZ_g2_true_witness
-- name    : SZ.g2_true_witness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:21:55.182202+00:00
-- url     : https://prove2.me/theorems/f53dc128-ae01-4521-a300-d8a7ebf995cd
-- title:
--   SZ: g2 true witness
-- statement:
--   The SZ construction uses the g2 true witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L738-L747
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L738-L747

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.g2_true_witness (β : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) (h : (node β k).g2 = true) :
    (node β j).g2 = true ∨ ∃ i, j ≤ i ∧ i < k ∧ (treeDigit β i).2 = 2 := by sorry
