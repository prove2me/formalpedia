-- Prove2me | Theorems.Thm_P2M_PI_SqPairLocal_StModel___ne_57ec0e9aa56c
-- name    : P2M_PI_SqPairLocal_StModel___ne_57ec0e9aa56c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:33:05.085528+00:00
-- url     : https://prove2.me/theorems/5da252d5-8e01-43c3-b352-8893217c62ba
-- title:
--   P2 M PI Sq Pair Local St Model   ne 57ec0e9aa56c: P2 M PI Sq Pair Local St Model   ne 57ec0e9aa56c
-- statement:
--   The P2 M PI Sq Pair Local St Model   ne 57ec0e9aa56c construction uses the P2 M PI Sq Pair Local St Model   ne 57ec0e9aa56c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L21-L25

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

theorem P2M_PI_SqPairLocal_StModel___ne_57ec0e9aa56c : M.ϖ ≠ 0 := by sorry

alias «PI».«SqPairLocal».«StModel».«ϖ_ne» := P2M_PI_SqPairLocal_StModel___ne_57ec0e9aa56c
