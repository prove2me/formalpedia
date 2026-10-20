-- Prove2me | Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_mul_le
-- name    : SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/0664e634-245d-4a9f-8cd0-9e2010abe39c
-- title:
--   SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_mul_le
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

theorem SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_mul_le
    {V : Type*} [Fintype V]
    (f : V → ℝ) (p q : Equiv.Perm V) :
    squaredPermutationEnergy f (p * q) ≤
      2 * squaredPermutationEnergy f p +
        2 * squaredPermutationEnergy f q := by sorry
