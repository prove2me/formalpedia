-- Prove2me | Theorems.Thm_SoficGroups_KunSharpThresholdCut_highCrossingProfile_eq_boundary
-- name    : SoficGroups.KunSharpThresholdCut.highCrossingProfile_eq_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/4e2d0656-44cc-4ad8-bebd-934da984b506
-- title:
--   SoficGroups.KunSharpThresholdCut.highCrossingProfile_eq_boundary
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

theorem SoficGroups.KunSharpThresholdCut.highCrossingProfile_eq_boundary {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a t : ℝ)
    (hat : a < t) :
    highCrossingProfile σ f a t =
      (SoficGroups.boundary σ (upperLevel f t) : ℝ) := by sorry
