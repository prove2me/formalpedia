-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_rpow_neg_half_eq
-- name    : PI.SqfRootsInj.W.rpow_neg_half_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:09.791112+00:00
-- url     : https://prove2.me/theorems/1babb329-583f-4522-b47e-bfe3bcc62a10
-- title:
--   W: rpow neg half eq
-- statement:
--   The W construction uses the rpow neg half eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/RpowQuarterPowFour.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/RpowQuarterPowFour.lean#L16-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_RpowQuarterPowFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab

theorem PI.SqfRootsInj.W.rpow_neg_half_eq (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = ((x ^ ((1 : ℝ) / 4))⁻¹) ^ 2 := by sorry
