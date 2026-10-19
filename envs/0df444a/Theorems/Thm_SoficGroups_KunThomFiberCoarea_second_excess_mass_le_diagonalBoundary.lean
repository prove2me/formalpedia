-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_second_excess_mass_le_diagonalBoundary
-- name    : SoficGroups.KunThomFiberCoarea.second_excess_mass_le_diagonalBoundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/8ec71554-5de8-4178-bac0-c81c1c970e18
-- title:
--   SoficGroups.KunThomFiberCoarea.second_excess_mass_le_diagonalBoundary
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.second_excess_mass_le_diagonalBoundary
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V)) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hsingle : Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card) :
    h * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) ≤
      (SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by sorry
