-- Prove2me | Theorems.Thm_PI_EF_Rect_le_of_mem_rectOpen
-- name    : PI.EF.Rect.le_of_mem_rectOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:33.207984+00:00
-- url     : https://prove2.me/theorems/c2da6cd6-d069-4969-bdb2-32413efbd74d
-- title:
--   Rect: le of mem rect Open
-- statement:
--   The Rect construction uses the le of mem rect Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L248-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L248-L250

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

theorem PI.EF.Rect.le_of_mem_rectOpen {z w p : ℂ} (hp : p ∈ rectOpen z w) : z.re ≤ w.re ∧ z.im ≤ w.im := by sorry
