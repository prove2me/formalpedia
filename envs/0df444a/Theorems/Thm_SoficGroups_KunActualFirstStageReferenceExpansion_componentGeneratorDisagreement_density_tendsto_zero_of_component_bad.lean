-- Prove2me | Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_componentGeneratorDisagreement_density_tendsto_zero_of_component_bad
-- name    : SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_density_tendsto_zero_of_component_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/cd60390c-3a2a-41b6-bb0c-e37277b260c1
-- title:
--   SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_density_tendsto_zero_of_component_bad
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

theorem SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_density_tendsto_zero_of_component_bad
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C B : (n : ℕ) → Finset (V n))
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (hbad : ∀ n i (x : V n), x ∈ C n →
      σref n i x ≠ σact n i x → x ∈ B n)
    (hdensity : Tendsto
      (fun n => (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (componentGeneratorDisagreement
          (C n) (σref n) (σact n) : ℝ) / (C n).card)
      atTop (nhds 0) := by sorry
