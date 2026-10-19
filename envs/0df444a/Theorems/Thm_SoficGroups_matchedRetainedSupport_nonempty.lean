-- Prove2me | Theorems.Thm_SoficGroups_matchedRetainedSupport_nonempty
-- name    : SoficGroups.matchedRetainedSupport_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/feddd18a-58b1-485b-b4f3-3aa189848e41
-- title:
--   SoficGroups.matchedRetainedSupport_nonempty
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

theorem SoficGroups.matchedRetainedSupport_nonempty
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (hRne : R.Nonempty) :
    (matchedRetainedSupport R).Nonempty := by sorry
