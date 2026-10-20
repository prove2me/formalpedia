-- Prove2me | Theorems.Thm_SoficGroups_matchedCore_subset_retainedSupport
-- name    : SoficGroups.matchedCore_subset_retainedSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/0b4691f7-b535-4e6f-b668-6b97e5b9a570
-- title:
--   SoficGroups.matchedCore_subset_retainedSupport
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

theorem SoficGroups.matchedCore_subset_retainedSupport
    {V : Type*} [DecidableEq V]
    (R : Finset (Finset V)) (D : Finset V → Finset V) :
    matchedCore R D ⊆ matchedRetainedSupport R := by sorry
