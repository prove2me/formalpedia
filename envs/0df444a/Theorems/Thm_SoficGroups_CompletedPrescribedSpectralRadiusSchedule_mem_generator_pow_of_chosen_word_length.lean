-- Prove2me | Theorems.Thm_SoficGroups_CompletedPrescribedSpectralRadiusSchedule_mem_generator_pow_of_chosen_word_length
-- name    : SoficGroups.CompletedPrescribedSpectralRadiusSchedule.mem_generator_pow_of_chosen_word_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/4ed7e98c-06ae-4189-b558-1fb05d70502f
-- title:
--   SoficGroups.CompletedPrescribedSpectralRadiusSchedule.mem_generator_pow_of_chosen_word_length
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedPrescribedSpectralRadiusSchedule
open Filter Topology
open scoped Pointwise

theorem SoficGroups.CompletedPrescribedSpectralRadiusSchedule.mem_generator_pow_of_chosen_word_length
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ a : G,
      ((w a).map fun i : ↥S => (i : G)).prod = a)
    {a : G} {r : ℕ} (ha : (w a).length ≤ r) :
    a ∈ S ^ r := by sorry
