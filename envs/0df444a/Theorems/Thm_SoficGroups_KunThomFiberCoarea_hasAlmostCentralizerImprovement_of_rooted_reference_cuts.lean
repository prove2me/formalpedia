-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_hasAlmostCentralizerImprovement_of_rooted_reference_cuts
-- name    : SoficGroups.KunThomFiberCoarea.hasAlmostCentralizerImprovement_of_rooted_reference_cuts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/292b871e-b4b4-4fbf-ae8f-73bd505030a0
-- title:
--   SoficGroups.KunThomFiberCoarea.hasAlmostCentralizerImprovement_of_rooted_reference_cuts
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.hasAlmostCentralizerImprovement_of_rooted_reference_cuts
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hcut : ∀ p : Equiv.Perm V,
      SoficGroups.permutationCommutationDefect σ p ≤ 2 * tolerance →
        ∃ U : Finset (V × V),
          2 * ((U \ SoficGroups.permutationGraph p).card +
            (SoficGroups.permutationGraph p \ U).card) ≤
              Fintype.card V ∧
          (h + 8 * (Fintype.card ι : ℝ)) *
              (SoficGroups.boundary
                (fun i => (σ i).prodCongr (σ i)) U : ℝ) ≤
            h * (tolerance : ℝ) ∧
          (5 : ℝ) *
              (4 * (SoficGroups.boundary
                (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
                h * ((U \ SoficGroups.permutationGraph p).card : ℝ)) ≤
            h * (Fintype.card V : ℝ)) :
    SoficGroups.HasAlmostCentralizerImprovement σ tolerance := by sorry
