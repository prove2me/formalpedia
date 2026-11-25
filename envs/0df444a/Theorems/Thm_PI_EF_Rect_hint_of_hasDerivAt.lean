-- Prove2me | Theorems.Thm_PI_EF_Rect_hint_of_hasDerivAt
-- name    : PI.EF.Rect.hint_of_hasDerivAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:44.134248+00:00
-- url     : https://prove2.me/theorems/85a78d74-7f7a-49e1-9eaa-f77c059fe5cf
-- title:
--   Rect: hint of has Deriv At
-- statement:
--   The Rect construction uses the hint of has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L27-L37

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

theorem PI.EF.Rect.hint_of_hasDerivAt {F f : ℂ → ℂ} {a₁ a₂ b : ℝ}
    (h : ∀ x ∈ uIcc a₁ a₂, HasDerivAt F (f (x + b * I)) (x + b * I))
    (hc : ∀ x ∈ uIcc a₁ a₂, ContinuousAt f (x + b * I)) :
    ∫ x : ℝ in a₁..a₂, f (x + b * I) = F (a₂ + b * I) - F (a₁ + b * I) := by sorry
