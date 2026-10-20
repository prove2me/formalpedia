-- Prove2me | Theorems.Thm_SoficGroups_KunSharpThresholdCut_setIntegral_highCrossingProfile_le_variation
-- name    : SoficGroups.KunSharpThresholdCut.setIntegral_highCrossingProfile_le_variation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/fd02d438-51dd-47e6-a0d6-84bfa8a1d623
-- title:
--   SoficGroups.KunSharpThresholdCut.setIntegral_highCrossingProfile_le_variation
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSharpThresholdCut
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff

theorem SoficGroups.KunSharpThresholdCut.setIntegral_highCrossingProfile_le_variation {V ι : Type*}
    [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a c d : ℝ) :
    (∫ t in Ioo c d, highCrossingProfile σ f a t) ≤
      ∑ i : ι, ∑ x ∈ Finset.univ.filter (fun x : V => a < f x),
        |f (σ i x) - f x| := by sorry
