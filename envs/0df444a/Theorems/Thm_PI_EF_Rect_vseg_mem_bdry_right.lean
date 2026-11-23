-- Prove2me | Theorems.Thm_PI_EF_Rect_vseg_mem_bdry_right
-- name    : PI.EF.Rect.vseg_mem_bdry_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:34.120803+00:00
-- url     : https://prove2.me/theorems/4af582c8-fcea-4c1a-b446-b6067d9b39bf
-- title:
--   Rect: vseg mem bdry right
-- statement:
--   The Rect construction uses the vseg mem bdry right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L75-L78

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

theorem PI.EF.Rect.vseg_mem_bdry_right {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((w.re : ℂ) + y * I) ∈ rectBdry z w := by sorry
