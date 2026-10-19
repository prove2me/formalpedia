-- Prove2me | Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_inv
-- name    : SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_inv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/72e05f8a-8422-4aa3-85ba-56a257e8fe3a
-- title:
--   SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_inv
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

theorem SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_inv
    {V : Type*} [Fintype V] (f : V → ℝ) (p : Equiv.Perm V) :
    squaredPermutationEnergy f p⁻¹ = squaredPermutationEnergy f p := by sorry
