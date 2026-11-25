-- Prove2me | Theorems.Thm_PI_SqPairLocal_StModel_notMem_of_unit
-- name    : PI.SqPairLocal.StModel.notMem_of_unit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:55.401858+00:00
-- url     : https://prove2.me/theorems/160b1ab5-6253-49fc-be67-69231d5973b7
-- title:
--   St Model: not Mem of unit
-- statement:
--   The St Model construction uses the not Mem of unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L27-L41

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
open PI.SqPairLocal.StModel
variable {Q : Ideal (𝓞 E)} (M : StModel E Q)

theorem PI.SqPairLocal.StModel.notMem_of_unit {x : 𝓞 E} (hx : IsUnit (M.j x)) : x ∉ Q := by sorry
