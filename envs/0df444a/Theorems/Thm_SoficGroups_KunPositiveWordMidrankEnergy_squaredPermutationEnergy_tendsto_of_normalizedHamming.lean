-- Prove2me | Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_tendsto_of_normalizedHamming
-- name    : SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_tendsto_of_normalizedHamming
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/9133486b-d0d0-4150-b2ce-6d052da72af6
-- title:
--   SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_tendsto_of_normalizedHamming
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

theorem SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_tendsto_of_normalizedHamming
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (f : (n : ℕ) → V n → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (p q : (n : ℕ) → Equiv.Perm (V n))
    (hq : Tendsto
      (fun n => squaredPermutationEnergy (f n) (q n) /
        Fintype.card (V n)) atTop (𝓝 0))
    (hd : Tendsto
      (fun n => SoficGroups.normalizedHamming (p n) (q n))
      atTop (𝓝 0)) :
    Tendsto
      (fun n => squaredPermutationEnergy (f n) (p n) /
        Fintype.card (V n)) atTop (𝓝 0) := by sorry
