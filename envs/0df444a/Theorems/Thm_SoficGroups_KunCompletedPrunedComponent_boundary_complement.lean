-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_boundary_complement
-- name    : SoficGroups.KunCompletedPrunedComponent.boundary_complement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/7c480aca-5639-4d35-a06f-1ede5f3e44b7
-- title:
--   SoficGroups.KunCompletedPrunedComponent.boundary_complement
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedPrunedComponent
open scoped BigOperators

theorem SoficGroups.KunCompletedPrunedComponent.boundary_complement
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) :
    SoficGroups.boundary σ (Finset.univ \ A) =
      SoficGroups.boundary σ A := by sorry
