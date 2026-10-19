-- Prove2me | Theorems.Thm_SoficGroups_target_majority_of_small_symmDiff
-- name    : SoficGroups.target_majority_of_small_symmDiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/c9e7d3b9-41ea-4fc4-8f45-b838ecc65c3b
-- title:
--   SoficGroups.target_majority_of_small_symmDiff
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

theorem SoficGroups.target_majority_of_small_symmDiff
    {V : Type*} [DecidableEq V] (C D : Finset V)
    (hsmall : 2 * (C ∆ D).card < C.card) :
    D.card < 2 * (C ∩ D).card := by sorry
