-- Prove2me | Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_sofic_action_inverse_normalizedHamming_tendsto_zero
-- name    : SoficGroups.KunPositiveWordMidrankEnergy.sofic_action_inverse_normalizedHamming_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/36ed6542-93a7-42d6-9fc6-e27d7699986f
-- title:
--   SoficGroups.KunPositiveWordMidrankEnergy.sofic_action_inverse_normalizedHamming_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunPositiveWordMidrankEnergy.sofic_action_inverse_normalizedHamming_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (g : G) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹)))
      atTop (𝓝 0) := by sorry
