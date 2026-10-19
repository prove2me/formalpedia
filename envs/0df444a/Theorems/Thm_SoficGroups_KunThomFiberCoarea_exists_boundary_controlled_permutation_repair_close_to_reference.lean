-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_exists_boundary_controlled_permutation_repair_close_to_reference
-- name    : SoficGroups.KunThomFiberCoarea.exists_boundary_controlled_permutation_repair_close_to_reference
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/bf61eb28-c86c-4854-9d59-fa2eab2074e2
-- title:
--   SoficGroups.KunThomFiberCoarea.exists_boundary_controlled_permutation_repair_close_to_reference
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.exists_boundary_controlled_permutation_repair_close_to_reference
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V))
    (p : Equiv.Perm V) (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hfirst : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card)
    (hsecond : Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card) :
    ∃ q : Equiv.Perm V,
      h * (SoficGroups.permutationDistance q p : ℝ) ≤
          4 * (SoficGroups.boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
            h * ((U \ SoficGroups.permutationGraph p).card : ℝ) ∧
        h * (SoficGroups.permutationCommutationDefect σ q : ℝ) ≤
          (h + 8 * (Fintype.card ι : ℝ)) *
            (SoficGroups.boundary
              (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by sorry
