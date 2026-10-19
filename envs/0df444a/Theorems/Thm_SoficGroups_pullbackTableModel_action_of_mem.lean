-- Prove2me | Theorems.Thm_SoficGroups_pullbackTableModel_action_of_mem
-- name    : SoficGroups.pullbackTableModel_action_of_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/960fa527-2b6b-4a8d-85bb-0c8211d20495
-- title:
--   SoficGroups.pullbackTableModel_action_of_mem
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

theorem SoficGroups.pullbackTableModel_action_of_mem {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F)
    (M : PermutationModel (tableGroup F h₁))
    {g : G} (hg : g ∈ multiplicationTable F) :
    (pullbackTableModel F h₁ M).action g =
      M.action (tableGenerator F h₁ ⟨g, hg⟩) := by sorry
