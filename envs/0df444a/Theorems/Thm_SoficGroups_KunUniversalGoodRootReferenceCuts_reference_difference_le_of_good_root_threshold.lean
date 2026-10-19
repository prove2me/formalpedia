-- Prove2me | Theorems.Thm_SoficGroups_KunUniversalGoodRootReferenceCuts_reference_difference_le_of_good_root_threshold
-- name    : SoficGroups.KunUniversalGoodRootReferenceCuts.reference_difference_le_of_good_root_threshold
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/006dc080-9f69-4d1a-b5a6-88f802bcdbce
-- title:
--   SoficGroups.KunUniversalGoodRootReferenceCuts.reference_difference_le_of_good_root_threshold
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUniversalGoodRootReferenceCuts
open scoped symmDiff

theorem SoficGroups.KunUniversalGoodRootReferenceCuts.reference_difference_le_of_good_root_threshold
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (p : Equiv.Perm V)
    (B : Finset V) (T U : Finset (V × V))
    (t : ℕ) (q : ℝ) (hq : q < 1)
    (hsub : T ⊆ SoficGroups.permutationGraph p)
    (hmissing :
      (SoficGroups.permutationGraph p \ T).card ≤ 2 * B.card)
    (hbad :
      2 * (Fintype.card ι : ℝ) * (B.card : ℝ) ≤ (t : ℝ))
    (hdefect : SoficGroups.permutationCommutationDefect σ p ≤ 2 * t)
    (hboundary :
      SoficGroups.boundary (fun i => (σ i).prodCongr (σ i)) T ≤
        SoficGroups.permutationCommutationDefect σ p +
          2 * Fintype.card ι * B.card)
    (hthreshold :
      ((U ∆ T).card : ℝ) ≤
        72 * (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) T : ℝ) /
            ((Fintype.card ι : ℝ) * (1 - q) ^ 2)) :
    (((U \ SoficGroups.permutationGraph p).card +
      (SoficGroups.permutationGraph p \ U).card : ℕ) : ℝ) ≤
        (216 / ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card ι : ℝ)) * (t : ℝ) := by sorry
