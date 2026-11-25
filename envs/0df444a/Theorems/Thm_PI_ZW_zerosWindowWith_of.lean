-- Prove2me | Theorems.Thm_PI_ZW_zerosWindowWith_of
-- name    : PI.ZW.zerosWindowWith_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:33.050885+00:00
-- url     : https://prove2.me/theorems/fda2a67a-1e05-48c9-8694-2eb2b805d772
-- title:
--   ZW: zeros Window With of
-- statement:
--   The ZW construction uses the zeros Window With of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L32-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L32-L79

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ZW
open DirichletCharacter

theorem PI.ZW.zerosWindowWith_of (C : ℝ) (hR : RightHalfWith C) (hT : Transfer) :
    PI.ZerosWindowWith (2 * C) := by sorry
