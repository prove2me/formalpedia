-- Prove2me | Theorems.Thm_SoficGroups_tableGroup_finitelyPresented
-- name    : SoficGroups.tableGroup_finitelyPresented
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/4b351978-e240-44be-b2d0-836afdc4bc46
-- title:
--   SoficGroups.tableGroup_finitelyPresented
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

theorem SoficGroups.tableGroup_finitelyPresented {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) :
    Group.IsFinitelyPresented (tableGroup F h₁) := by sorry
