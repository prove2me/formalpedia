-- Prove2me | Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_componentGeneratorDisagreement_comm
-- name    : SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/f854e0c4-5c14-44d7-8983-a12023076384
-- title:
--   SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_comm
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_comm
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (C : Finset V)
    (σref σact : ι → Equiv.Perm V) :
    componentGeneratorDisagreement C σref σact =
      componentGeneratorDisagreement C σact σref := by sorry
