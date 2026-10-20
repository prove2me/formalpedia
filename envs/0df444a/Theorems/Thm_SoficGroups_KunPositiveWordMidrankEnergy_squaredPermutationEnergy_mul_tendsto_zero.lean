-- Prove2me | Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_mul_tendsto_zero
-- name    : SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_mul_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/b9d85eda-f209-4353-93c5-200578047339
-- title:
--   SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_mul_tendsto_zero
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

theorem SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_mul_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    (f : (n : ℕ) → V n → ℝ)
    (p q : (n : ℕ) → Equiv.Perm (V n))
    (hp : Tendsto
      (fun n => squaredPermutationEnergy (f n) (p n) /
        Fintype.card (V n)) atTop (𝓝 0))
    (hq : Tendsto
      (fun n => squaredPermutationEnergy (f n) (q n) /
        Fintype.card (V n)) atTop (𝓝 0)) :
    Tendsto
      (fun n => squaredPermutationEnergy (f n) (p n * q n) /
        Fintype.card (V n)) atTop (𝓝 0) := by sorry
