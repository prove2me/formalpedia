-- Prove2me | Theorems.Thm_SZ_node_used_mono
-- name    : SZ.node_used_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:31.949083+00:00
-- url     : https://prove2.me/theorems/89926dd7-4abd-4da9-aa24-6f79e5e319e4
-- title:
--   SZ: node used mono
-- statement:
--   The SZ construction uses the node used mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1048-L1055
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1048-L1055

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_used_mono (β : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) :
    (node β j).used ≤ (node β k).used := by sorry
