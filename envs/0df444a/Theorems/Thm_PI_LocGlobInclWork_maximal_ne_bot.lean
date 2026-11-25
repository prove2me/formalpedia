-- Prove2me | Theorems.Thm_PI_LocGlobInclWork_maximal_ne_bot
-- name    : PI.LocGlobInclWork.maximal_ne_bot
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:16.362603+00:00
-- url     : https://prove2.me/theorems/8afda13e-e16f-503d-8f73-7825cffe6be1
-- title:
--   Loc Glob Incl Work: maximal ne bot
-- statement:
--   The Loc Glob Incl Work construction uses the maximal ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L20-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]

theorem PI.LocGlobInclWork.maximal_ne_bot (m : Ideal (𝓞 K)) (hm : m.IsMaximal) : m ≠ ⊥ := by sorry
