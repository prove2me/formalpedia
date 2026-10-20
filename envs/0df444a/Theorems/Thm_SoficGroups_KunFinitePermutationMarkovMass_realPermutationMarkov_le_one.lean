-- Prove2me | Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_realPermutationMarkov_le_one
-- name    : SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/f18a7e4c-ba40-41ee-b0ef-9b7ad85c4eed
-- title:
--   SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_le_one
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators

theorem SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_le_one {V ι : Type*}
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x ≤ 1) (x : V) :
    realPermutationMarkov σ f x ≤ 1 := by sorry
