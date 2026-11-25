-- Prove2me | Theorems.Thm_SZ_node_g0_mono
-- name    : SZ.node_g0_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:19:00.86709+00:00
-- url     : https://prove2.me/theorems/26d0110a-76a9-5e05-bc1e-59b152f5953a
-- title:
--   SZ: node g0 mono
-- statement:
--   Without branchings the flags only ever go up.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L750-L758
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L750-L758

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_g0_mono (β : ℕ → Bool) {N : ℕ} (hno : ∀ i, ¬ Branching (node β (N + i)))
    {j k : ℕ} (hjk : j ≤ k) (h0 : (node β (N + j)).g0 = true) :
    (node β (N + k)).g0 = true := by sorry
