-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationVariation_subtract_layer
-- name    : SoficGroups.KunThomFiberCoarea.permutationVariation_subtract_layer
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/789ada4e-a746-48df-bb0d-7877d77190ea
-- title:
--   SoficGroups.KunThomFiberCoarea.permutationVariation_subtract_layer
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.permutationVariation_subtract_layer
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (f : V → ℕ)
    (A : Finset V) (m : ℕ)
    (hinside : ∀ x ∈ A, m ≤ f x)
    (houtside : ∀ x, x ∉ A → f x = 0) :
    permutationVariation σ f =
      permutationVariation σ
          (fun x => if x ∈ A then f x - m else 0) +
        2 * m * SoficGroups.boundary σ A := by sorry
