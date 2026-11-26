-- Prove2me | Theorems.Thm_P2M_RH_PI_SqPairLocal_coe_cj_5529f146e9bab632
-- name    : P2M_RH_PI_SqPairLocal_coe_cj_5529f146e9bab632
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:18.21668+00:00
-- url     : https://prove2.me/theorems/a475a4d9-7a8c-5f37-ad7a-b9749c6b3b4e
-- title:
--   P2 M RH PI Sq Pair Local coe cj 5529f146e9bab632: P2 M RH PI Sq Pair Local coe cj 5529f146e9bab632
-- statement:
--   The P2 M RH PI Sq Pair Local coe cj 5529f146e9bab632 construction uses the P2 M RH PI Sq Pair Local coe cj 5529f146e9bab632 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L15-L15

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

theorem P2M_RH_PI_SqPairLocal_coe_cj_5529f146e9bab632 (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := by sorry

alias «PI».«SqPairLocal».«coe_cj» := P2M_RH_PI_SqPairLocal_coe_cj_5529f146e9bab632
