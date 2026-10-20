-- Prove2me | Theorems.Thm_SoficGroups_tableGroup_not_sofic_of_obstruction
-- name    : SoficGroups.tableGroup_not_sofic_of_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/27bb5c28-8488-4ada-aa22-0976e8b6095d
-- title:
--   SoficGroups.tableGroup_not_sofic_of_obstruction
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

theorem SoficGroups.tableGroup_not_sofic_of_obstruction {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1)
    (hbad : ∀ M : PermutationModel G, ¬ GoodOn M F ε) :
    ¬ Sofic (tableGroup F h₁) := by sorry
