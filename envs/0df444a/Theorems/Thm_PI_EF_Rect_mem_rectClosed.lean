-- Prove2me | Theorems.Thm_PI_EF_Rect_mem_rectClosed
-- name    : PI.EF.Rect.mem_rectClosed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:39.168961+00:00
-- url     : https://prove2.me/theorems/f129a3a7-b8a2-443e-bcc5-392334739055
-- title:
--   Rect: mem rect Closed
-- statement:
--   The Rect construction uses the mem rect Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L222-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L222-L224

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

theorem PI.EF.Rect.mem_rectClosed {z w s : ℂ} :
    s ∈ rectClosed z w ↔ (z.re ≤ s.re ∧ s.re ≤ w.re) ∧ (z.im ≤ s.im ∧ s.im ≤ w.im) := by sorry
