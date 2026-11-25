-- Prove2me | Theorems.Thm_PI_ZW_rightChi_of
-- name    : PI.ZW.rightChi_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:04.71634+00:00
-- url     : https://prove2.me/theorems/80f807d6-f8ef-4146-b56b-f7f213434e3e
-- title:
--   ZW: right Chi of
-- statement:
--   The ZW construction uses the right Chi of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightChi.lean#L47-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightChi.lean#L47-L94

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex
open PI PI.ZW

theorem PI.ZW.rightChi_of (hJ : JensenCount) : RightChi := by sorry
