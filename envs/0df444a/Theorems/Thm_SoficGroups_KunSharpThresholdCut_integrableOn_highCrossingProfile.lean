-- Prove2me | Theorems.Thm_SoficGroups_KunSharpThresholdCut_integrableOn_highCrossingProfile
-- name    : SoficGroups.KunSharpThresholdCut.integrableOn_highCrossingProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/c3892032-9561-429d-aefd-8a0a1c0e2f0b
-- title:
--   SoficGroups.KunSharpThresholdCut.integrableOn_highCrossingProfile
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

theorem SoficGroups.KunSharpThresholdCut.integrableOn_highCrossingProfile {V ι : Type*}
    [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a c d : ℝ) :
    IntegrableOn (highCrossingProfile σ f a) (Ioo c d) := by sorry
