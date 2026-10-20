-- Prove2me | Theorems.Thm_SoficGroups_KunSharpThresholdCut_integrableOn_crossingIndicator
-- name    : SoficGroups.KunSharpThresholdCut.integrableOn_crossingIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/80c537ea-626f-4248-b733-3dafe3ffa44e
-- title:
--   SoficGroups.KunSharpThresholdCut.integrableOn_crossingIndicator
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

theorem SoficGroups.KunSharpThresholdCut.integrableOn_crossingIndicator
    (a b c d : ℝ) :
    IntegrableOn ((Ico a b).indicator (fun _ => (1 : ℝ)))
      (Ioo c d) := by sorry
