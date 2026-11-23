-- Prove2me | Theorems.Thm_PI_EF_Rect_rectInt_congr
-- name    : PI.EF.Rect.rectInt_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:58.588734+00:00
-- url     : https://prove2.me/theorems/733810c8-c7a8-4850-a272-ebb06d3d5bb9
-- title:
--   Rect: rect Int congr
-- statement:
--   The Rect construction uses the rect Int congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L176-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L176-L182

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

theorem PI.EF.Rect.rectInt_congr {f g : ℂ → ℂ} {z w : ℂ} (h : EqOn f g (rectBdry z w)) :
    rectInt f z w = rectInt g z w := by sorry
