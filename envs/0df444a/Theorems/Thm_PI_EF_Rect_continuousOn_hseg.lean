-- Prove2me | Theorems.Thm_PI_EF_Rect_continuousOn_hseg
-- name    : PI.EF.Rect.continuousOn_hseg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:33.049386+00:00
-- url     : https://prove2.me/theorems/a249cd07-9185-40f3-9fd9-c9e27d473f5b
-- title:
--   Rect: continuous On hseg
-- statement:
--   The Rect construction uses the continuous On hseg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L13-L18

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

theorem PI.EF.Rect.continuousOn_hseg {f : ℂ → ℂ} {a₁ a₂ b : ℝ}
    (hc : ∀ x ∈ uIcc a₁ a₂, ContinuousAt f (x + b * I)) :
    ContinuousOn (fun x : ℝ => f (x + b * I)) (uIcc a₁ a₂) := by sorry
