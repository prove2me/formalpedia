-- Prove2me | Theorems.Thm_PI_EF_Rect_rectBdry_subset
-- name    : PI.EF.Rect.rectBdry_subset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:28.269621+00:00
-- url     : https://prove2.me/theorems/14cc8f3a-433b-4945-95a7-e4bcf6a8fdca
-- title:
--   Rect: rect Bdry subset
-- statement:
--   The Rect construction uses the rect Bdry subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L238-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L238-L246

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

theorem PI.EF.Rect.rectBdry_subset {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    rectBdry z w ⊆ rectClosed z w := by sorry
