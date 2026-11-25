-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_dop_comm
-- name    : PI.HookSteps.Cap.dop_comm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:30.115036+00:00
-- url     : https://prove2.me/theorems/411c73e8-4360-46e1-80dd-aed3d528f89f
-- title:
--   Cap: dop comm
-- statement:
--   The Cap construction uses the dop comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliOps.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliOps.lean#L42-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open MvPolynomial Finset

theorem PI.HookSteps.Cap.dop_comm (N : ℕ) (b t b' t' : Fin N) : Commute (dop N b t) (dop N b' t') := by sorry
