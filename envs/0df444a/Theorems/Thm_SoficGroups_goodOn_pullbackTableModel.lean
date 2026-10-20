-- Prove2me | Theorems.Thm_SoficGroups_goodOn_pullbackTableModel
-- name    : SoficGroups.goodOn_pullbackTableModel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/34b94364-25eb-409d-a596-ad73b9cc5b90
-- title:
--   SoficGroups.goodOn_pullbackTableModel
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

theorem SoficGroups.goodOn_pullbackTableModel {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) {ε : ℝ}
    (M : PermutationModel (tableGroup F h₁))
    (hM : GoodOn M (tableTestSet F h₁) ε) :
    GoodOn (pullbackTableModel F h₁ M) F ε := by sorry
