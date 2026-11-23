-- Prove2me | Theorems.Thm_PI_EF_Rect_rectClosed_mem_nhds
-- name    : PI.EF.Rect.rectClosed_mem_nhds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:50.987489+00:00
-- url     : https://prove2.me/theorems/4dda684e-56cf-40cc-829f-44acd0cf02d6
-- title:
--   Rect: rect Closed mem nhds
-- statement:
--   The Rect construction uses the rect Closed mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L230-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L230-L236

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

theorem PI.EF.Rect.rectClosed_mem_nhds {z w p : ℂ} (hp : p ∈ rectOpen z w) : rectClosed z w ∈ 𝓝 p := by sorry
