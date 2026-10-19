-- Prove2me | Theorems.Thm_SoficGroups_partitionComponentSize_eq_card_of_mem
-- name    : SoficGroups.partitionComponentSize_eq_card_of_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/6651ae45-8a8c-4ac5-8d13-d185dbbd0748
-- title:
--   SoficGroups.partitionComponentSize_eq_card_of_mem
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

theorem SoficGroups.partitionComponentSize_eq_card_of_mem
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V) (hC : C ∈ Q.parts)
    (x : V) (hx : x ∈ C) :
    partitionComponentSize Q x = C.card := by sorry
