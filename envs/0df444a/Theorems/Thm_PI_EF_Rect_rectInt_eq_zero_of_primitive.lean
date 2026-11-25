-- Prove2me | Theorems.Thm_PI_EF_Rect_rectInt_eq_zero_of_primitive
-- name    : PI.EF.Rect.rectInt_eq_zero_of_primitive
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:52.302045+00:00
-- url     : https://prove2.me/theorems/a99fd17b-bec2-4303-987b-a5015bb6007b
-- title:
--   Rect: rect Int eq zero of primitive
-- statement:
--   The Rect construction uses the rect Int eq zero of primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L80-L88

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

theorem PI.EF.Rect.rectInt_eq_zero_of_primitive {F f : ℂ → ℂ} {z w : ℂ}
    (h : ∀ s ∈ rectBdry z w, HasDerivAt F (f s) s) (hc : ∀ s ∈ rectBdry z w, ContinuousAt f s) :
    rectInt f z w = 0 := by sorry
