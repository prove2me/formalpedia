-- Prove2me | Theorems.Thm_SoficGroups_KunSharpThresholdCut_exists_upperLevel_boundary_and_symmDiff_le
-- name    : SoficGroups.KunSharpThresholdCut.exists_upperLevel_boundary_and_symmDiff_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/ab3c33cf-8fc7-4b7e-8fa2-a70454b5ea5d
-- title:
--   SoficGroups.KunSharpThresholdCut.exists_upperLevel_boundary_and_symmDiff_le
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

theorem SoficGroups.KunSharpThresholdCut.exists_upperLevel_boundary_and_symmDiff_le {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ) :
    ∃ t ∈ Ioo (1 / 3 : ℝ) (2 / 3 : ℝ),
      (SoficGroups.boundary σ (upperLevel f t) : ℝ) ≤
          3 * ∑ i : ι,
            ∑ x ∈ Finset.univ.filter
              (fun x : V => (1 / 3 : ℝ) < f x),
                |f (σ i x) - f x| ∧
        (((upperLevel f t ∆ T).card : ℝ)) ≤
          9 * ∑ x : V,
            (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by sorry
