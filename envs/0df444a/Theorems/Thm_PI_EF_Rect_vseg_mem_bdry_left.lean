-- Prove2me | Theorems.Thm_PI_EF_Rect_vseg_mem_bdry_left
-- name    : PI.EF.Rect.vseg_mem_bdry_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:31.8378+00:00
-- url     : https://prove2.me/theorems/9438f4b8-ae16-4232-a1a3-8bb9527efa95
-- title:
--   Rect: vseg mem bdry left
-- statement:
--   The Rect construction uses the vseg mem bdry left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L70-L73

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

theorem PI.EF.Rect.vseg_mem_bdry_left {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((z.re : ℂ) + y * I) ∈ rectBdry z w := by sorry
