-- Prove2me | Theorems.Thm_PI_EF_Rect_rectOpen_eq
-- name    : PI.EF.Rect.rectOpen_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:47.289716+00:00
-- url     : https://prove2.me/theorems/e265d490-be0d-4766-b902-58027607e262
-- title:
--   Rect: rect Open eq
-- statement:
--   The Rect construction uses the rect Open eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L226-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L226-L228

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

theorem PI.EF.Rect.rectOpen_eq (z w : ℂ) : rectOpen z w = Ioo z.re w.re ×ℂ Ioo z.im w.im := by sorry
