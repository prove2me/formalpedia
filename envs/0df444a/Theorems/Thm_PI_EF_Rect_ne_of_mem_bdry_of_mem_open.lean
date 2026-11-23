-- Prove2me | Theorems.Thm_PI_EF_Rect_ne_of_mem_bdry_of_mem_open
-- name    : PI.EF.Rect.ne_of_mem_bdry_of_mem_open
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:03.403927+00:00
-- url     : https://prove2.me/theorems/960aa498-d91f-45d3-a3d9-8a61801aad8f
-- title:
--   Rect: ne of mem bdry of mem open
-- statement:
--   The Rect construction uses the ne of mem bdry of mem open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L94-L98

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

theorem PI.EF.Rect.ne_of_mem_bdry_of_mem_open {z w s p : ℂ} (hs : s ∈ rectBdry z w) (hp : p ∈ rectOpen z w) :
    s ≠ p := by sorry
