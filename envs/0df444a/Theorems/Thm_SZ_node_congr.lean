-- Prove2me | Theorems.Thm_SZ_node_congr
-- name    : SZ.node_congr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:40:29.08198+00:00
-- url     : https://prove2.me/theorems/19c96a37-46a4-4589-981a-8da6d3d637fc
-- title:
--   SZ: node congr
-- statement:
--   The SZ construction uses the node congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1089-L1106
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1089-L1106

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_congr {β β' : ℕ → Bool} {n : ℕ} (hagree : ∀ i, i < n → β i = β' i) :
    ∀ k, (node β k).used ≤ n → node β k = node β' k := by sorry
