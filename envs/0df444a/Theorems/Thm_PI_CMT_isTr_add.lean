-- Prove2me | Theorems.Thm_PI_CMT_isTr_add
-- name    : PI.CMT.isTr_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:26:12.22166+00:00
-- url     : https://prove2.me/theorems/4a801903-0917-4218-850a-375b4be55ef0
-- title:
--   CMT: is Tr add
-- statement:
--   The CMT construction uses the is Tr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMTraceSurjective/IsTrMulConjOfMem.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMTraceSurjective/IsTrMulConjOfMem.lean#L24-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]

theorem PI.CMT.isTr_add {s t : 𝓞 K} (hs : IsTr s) (ht : IsTr t) : IsTr (s + t) := by sorry
