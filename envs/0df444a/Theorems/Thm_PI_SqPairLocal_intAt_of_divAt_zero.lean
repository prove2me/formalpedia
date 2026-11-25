-- Prove2me | Theorems.Thm_PI_SqPairLocal_intAt_of_divAt_zero
-- name    : PI.SqPairLocal.intAt_of_divAt_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:40.600918+00:00
-- url     : https://prove2.me/theorems/4dad2fcc-2959-5a9a-a687-57dc0c1291e9
-- title:
--   Sq Pair Local: int At of div At zero
-- statement:
--   The Sq Pair Local construction uses the int At of div At zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L135-L138

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IntAtOfDivAtZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair
attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PI.SqPairLocal.intAt_of_divAt_zero {Q : Ideal (𝓞 E)} (ϖ : 𝓞 E) {x : E} (h : DivAt Q (ϖ ^ 0) x) :
    IntAt Q x := by sorry
