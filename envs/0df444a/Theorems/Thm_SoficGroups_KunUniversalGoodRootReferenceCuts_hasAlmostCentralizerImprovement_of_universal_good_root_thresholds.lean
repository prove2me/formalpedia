-- Prove2me | Theorems.Thm_SoficGroups_KunUniversalGoodRootReferenceCuts_hasAlmostCentralizerImprovement_of_universal_good_root_thresholds
-- name    : SoficGroups.KunUniversalGoodRootReferenceCuts.hasAlmostCentralizerImprovement_of_universal_good_root_thresholds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/d93a5b28-d6eb-436a-8b18-e5d499beea8f
-- title:
--   SoficGroups.KunUniversalGoodRootReferenceCuts.hasAlmostCentralizerImprovement_of_universal_good_root_thresholds
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUniversalGoodRootReferenceCuts
open scoped symmDiff

theorem SoficGroups.KunUniversalGoodRootReferenceCuts.hasAlmostCentralizerImprovement_of_universal_good_root_thresholds
    {V ι : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (h q : ℝ) (hpositive : 0 < h) (hq : q < 1)
    (B : Finset V)
    (good : Equiv.Perm V → Finset (V × V))
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hbad :
      2 * (Fintype.card ι : ℝ) * (B.card : ℝ) ≤
        (tolerance : ℝ))
    (hgood_subset : ∀ p : Equiv.Perm V,
      good p ⊆ SoficGroups.permutationGraph p)
    (hgood_missing : ∀ p : Equiv.Perm V,
      (SoficGroups.permutationGraph p \ good p).card ≤
        2 * B.card)
    (hgood_boundary : ∀ p : Equiv.Perm V,
      SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) (good p) ≤
          SoficGroups.permutationCommutationDefect σ p +
            2 * Fintype.card ι * B.card)
    (hslow :
      5 * (4 + h *
        (216 / ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card ι : ℝ))) * (tolerance : ℝ) ≤
            h * (Fintype.card V : ℝ))
    (hthreshold : ∀ p : Equiv.Perm V,
      SoficGroups.permutationCommutationDefect σ p ≤ 2 * tolerance →
        ∃ U : Finset (V × V),
          ((U ∆ good p).card : ℝ) ≤
            72 * (SoficGroups.boundary
              (fun i => (σ i).prodCongr (σ i)) (good p) : ℝ) /
                ((Fintype.card ι : ℝ) * (1 - q) ^ 2) ∧
          (SoficGroups.boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) ≤
              (h * (tolerance : ℝ) /
                (2 * (h + 8 * (Fintype.card ι : ℝ)) *
                  (Fintype.card V : ℝ))) * (U.card : ℝ)) :
    SoficGroups.HasAlmostCentralizerImprovement σ tolerance := by sorry
