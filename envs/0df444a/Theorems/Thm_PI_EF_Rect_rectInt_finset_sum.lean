-- Prove2me | Theorems.Thm_PI_EF_Rect_rectInt_finset_sum
-- name    : PI.EF.Rect.rectInt_finset_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:45.495809+00:00
-- url     : https://prove2.me/theorems/9c306310-9392-4691-a6eb-164c25917107
-- title:
--   Rect: rect Int finset sum
-- statement:
--   The Rect construction uses the rect Int finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L207-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L207-L220

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

theorem PI.EF.Rect.rectInt_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (hF : ∀ i ∈ S, ContinuousOn (F i) (rectBdry z w)) :
    rectInt (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, rectInt (F i) z w := by sorry
