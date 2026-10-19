-- Prove2me | Theorems.Thm_SoficGroups_mem_permutationGraph
-- name    : SoficGroups.mem_permutationGraph
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/31ec711b-7773-42cf-8172-a2ae30ece06d
-- title:
--   SoficGroups.mem_permutationGraph
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
universe u₁ u₂ u₃

theorem SoficGroups.mem_permutationGraph {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (x y : V) :
    (x, y) ∈ permutationGraph p ↔ y = p x := by sorry
