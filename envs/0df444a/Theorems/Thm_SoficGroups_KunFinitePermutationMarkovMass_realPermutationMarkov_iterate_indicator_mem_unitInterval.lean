-- Prove2me | Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_realPermutationMarkov_iterate_indicator_mem_unitInterval
-- name    : SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_indicator_mem_unitInterval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/2750e644-89d4-4e3c-8d8b-14f568a878e9
-- title:
--   SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_indicator_mem_unitInterval
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators

theorem SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_indicator_mem_unitInterval
    {V ι : Type*}
    [DecidableEq V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) (x : V) :
    0 ≤ ((realPermutationMarkov σ)^[k]) (realIndicator T) x ∧
      ((realPermutationMarkov σ)^[k]) (realIndicator T) x ≤ 1 := by sorry
