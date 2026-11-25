-- Prove2me | Theorems.Thm_PI_EF_Rect_continuousOn_vseg
-- name    : PI.EF.Rect.continuousOn_vseg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:31.898832+00:00
-- url     : https://prove2.me/theorems/5aab7c46-58ec-4ede-a4b1-3444447d9acf
-- title:
--   Rect: continuous On vseg
-- statement:
--   The Rect construction uses the continuous On vseg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L20-L25

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

theorem PI.EF.Rect.continuousOn_vseg {f : ℂ → ℂ} {a b₁ b₂ : ℝ}
    (hc : ∀ y ∈ uIcc b₁ b₂, ContinuousAt f (a + y * I)) :
    ContinuousOn (fun y : ℝ => f (a + y * I)) (uIcc b₁ b₂) := by sorry
