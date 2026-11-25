-- Prove2me | Theorems.Thm_SZ_node_st_of_not_branching
-- name    : SZ.node_st_of_not_branching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:37:20.184804+00:00
-- url     : https://prove2.me/theorems/b5cc3145-9a37-5880-8000-62dba87a7372
-- title:
--   SZ: node st of not branching
-- statement:
--   In a stretch without branchings the play is exactly the rule's orbit.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L693-L701
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L693-L701

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.node_st_of_not_branching (β : ℕ → Bool) {N : ℕ}
    (hno : ∀ i, ¬ Branching (node β (N + i))) (j : ℕ) :
    (node β (N + j)).st = gState (node β N).st j := by sorry
