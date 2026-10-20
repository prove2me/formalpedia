-- Prove2me | Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_le_add_hammingDist
-- name    : SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_le_add_hammingDist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/3fc1eaa2-a8d0-4c7c-a599-996e555f8dd2
-- title:
--   SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_le_add_hammingDist
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

theorem SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_le_add_hammingDist
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (p q : Equiv.Perm V) :
    squaredPermutationEnergy f p ≤
      squaredPermutationEnergy f q +
        (hammingDist (fun x => p x) (fun x => q x) : ℝ) := by sorry
