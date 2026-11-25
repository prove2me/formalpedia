-- Prove2me | Theorems.Thm_PI_EF_Rect_rectInt_inv_sub
-- name    : PI.EF.Rect.rectInt_inv_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:57.914155+00:00
-- url     : https://prove2.me/theorems/4ddb6a91-3c26-45c1-8382-4b669f03fe79
-- title:
--   Rect: rect Int inv sub
-- statement:
--   The Rect construction uses the rect Int inv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L124-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L124-L159

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

theorem PI.EF.Rect.rectInt_inv_sub {z w p : ℂ} (hp : p ∈ rectOpen z w) :
    rectInt (fun s => (s - p)⁻¹) z w = 2 * π * I := by sorry
