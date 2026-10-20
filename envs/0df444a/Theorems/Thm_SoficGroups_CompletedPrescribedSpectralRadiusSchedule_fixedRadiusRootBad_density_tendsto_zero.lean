-- Prove2me | Theorems.Thm_SoficGroups_CompletedPrescribedSpectralRadiusSchedule_fixedRadiusRootBad_density_tendsto_zero
-- name    : SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/ff514f34-3812-4662-9cdf-b9a3ed89a2c0
-- title:
--   SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_density_tendsto_zero
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

theorem SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_density_tendsto_zero
    {G : Type*} [Group G] [DecidableEq G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (φ : ∀ n, G → Equiv.Perm (V n))
    (S : Finset G)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (φ n (a * g)) (φ n a * φ n g))
        atTop (𝓝 0))
    (r : ℕ) :
    Tendsto
      (fun n =>
        ((fixedRadiusRootBad (φ n) S r).card : ℝ) /
          Fintype.card (V n))
      atTop (𝓝 0) := by sorry
