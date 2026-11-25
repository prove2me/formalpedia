-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_sums_le
-- name    : PI.SqfRootsInj.W.sums_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:44.646055+00:00
-- url     : https://prove2.me/theorems/1af144c7-af7d-5e0c-8cf1-5027ab1dc5ac
-- title:
--   W: sums le
-- statement:
--   The W construction uses the sums le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/RpowQuarterPowFour.lean#L75-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/RpowQuarterPowFour.lean#L75-L225

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

theorem PI.SqfRootsInj.W.sums_le (g r : ℕ) [hgp : Fact g.Prime] (hg : 2 ^ 12 ≤ g) :
    ((SA g r + SB g r : ℕ) : ℝ) ≤ 23 * Real.log g * (g : ℝ) ^ (-(1 / 2 : ℝ)) * (g : ℝ) ^ r := by sorry
