-- Prove2me | Theorems.Thm_SZ_exists_branch_at_used
-- name    : SZ.exists_branch_at_used
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:22:46.070302+00:00
-- url     : https://prove2.me/theorems/14a5e608-64e3-488d-ade0-fd624acfa1eb
-- title:
--   SZ: exists branch at used
-- statement:
--   The `n`-th bit is consumed at a genuine branching.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1069-L1085
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1069-L1085

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.exists_branch_at_used (β : ℕ → Bool) (n : ℕ) :
    ∃ k, (node β k).used = n ∧ Branching (node β k) := by sorry
