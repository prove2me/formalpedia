-- Prove2me | Theorems.Thm_SZ_g0_true_witness
-- name    : SZ.g0_true_witness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:18:47.367934+00:00
-- url     : https://prove2.me/theorems/1ab2f4ff-d350-5423-ac1e-7d26c7011c3e
-- title:
--   SZ: g0 true witness
-- statement:
--   A flag that is set was set by a digit actually emitted in the meantime.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L727-L736
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L727-L736

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.g0_true_witness (β : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) (h : (node β k).g0 = true) :
    (node β j).g0 = true ∨ ∃ i, j ≤ i ∧ i < k ∧ (treeDigit β i).1 = 0 := by sorry
