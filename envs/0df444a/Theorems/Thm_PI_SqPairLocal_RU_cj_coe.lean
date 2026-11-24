-- Prove2me | Theorems.Thm_PI_SqPairLocal_RU_cj_coe
-- name    : PI.SqPairLocal.RU.cj_coe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:27.440801+00:00
-- url     : https://prove2.me/theorems/42fd21ea-05b1-4357-bc72-93a3d2037fe4
-- title:
--   RU: cj coe
-- statement:
--   The RU construction uses the cj coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsConjugationFixedUniformizer.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsConjugationFixedUniformizer.lean#L11-L11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsConjugationFixedUniformizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal PI.SqPairLocal.RU
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PI.SqPairLocal.RU.cj_coe (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := by sorry
