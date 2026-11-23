-- Prove2me | Theorems.Thm_PI_EF_Rect_hseg_mem_bdry_bot
-- name    : PI.EF.Rect.hseg_mem_bdry_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:32.202807+00:00
-- url     : https://prove2.me/theorems/38bce896-eebc-45b3-9313-0c6a4d32e9b2
-- title:
--   Rect: hseg mem bdry bot
-- statement:
--   The Rect construction uses the hseg mem bdry bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L60-L63

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

theorem PI.EF.Rect.hseg_mem_bdry_bot {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    ((x : ℂ) + z.im * I) ∈ rectBdry z w := by sorry
