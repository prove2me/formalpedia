-- Prove2me | Theorems.Thm_SZ_node_g2_mono
-- name    : SZ.node_g2_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:19:06.791646+00:00
-- url     : https://prove2.me/theorems/ef9bfaa3-30cf-5e2c-8ad9-a4922ed99918
-- title:
--   SZ: node g2 mono
-- statement:
--   The SZ construction uses the node g2 mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L760-L768
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L760-L768

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_g2_mono (β : ℕ → Bool) {N : ℕ} (hno : ∀ i, ¬ Branching (node β (N + i)))
    {j k : ℕ} (hjk : j ≤ k) (h2 : (node β (N + j)).g2 = true) :
    (node β (N + k)).g2 = true := by sorry
