-- Prove2me | Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_componentGeneratorDisagreement_le_card_mul_component_bad
-- name    : SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_le_card_mul_component_bad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/d156f796-0e57-4388-8c3f-1532c6aac547
-- title:
--   SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_le_card_mul_component_bad
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

theorem SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_le_card_mul_component_bad
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (C B : Finset V)
    (σref σact : ι → Equiv.Perm V)
    (hbad : ∀ i (x : V), x ∈ C →
      σref i x ≠ σact i x → x ∈ B) :
    componentGeneratorDisagreement C σref σact ≤
      Fintype.card ι * (C ∩ B).card := by sorry
