-- Prove2me | Theorems.Thm_SZ_node_st_eq_runState
-- name    : SZ.node_st_eq_runState
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:36:00.667176+00:00
-- url     : https://prove2.me/theorems/84995890-d4a6-40c2-a2f1-4204dce0adec
-- title:
--   SZ: node st eq run State
-- statement:
--   The SZ construction uses the node st eq run State property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L643-L647
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L643-L647

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_st_eq_runState (β : ℕ → Bool) (k : ℕ) :
    (node β k).st = runState (-12, 9) (treeDigit β) k := by sorry
