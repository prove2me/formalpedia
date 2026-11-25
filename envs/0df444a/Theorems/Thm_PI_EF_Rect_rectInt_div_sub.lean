-- Prove2me | Theorems.Thm_PI_EF_Rect_rectInt_div_sub
-- name    : PI.EF.Rect.rectInt_div_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:13.355185+00:00
-- url     : https://prove2.me/theorems/03f264e8-d12b-4d2e-b95b-ef7679780229
-- title:
--   Rect: rect Int div sub
-- statement:
--   The Rect construction uses the rect Int div sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L275-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L275-L308

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real

theorem PI.EF.Rect.rectInt_div_sub {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : DifferentiableOn ℂ h (rectClosed z w)) :
    rectInt (fun s => h s / (s - p)) z w = 2 * π * I * h p := by sorry
