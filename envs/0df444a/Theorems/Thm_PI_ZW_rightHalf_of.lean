-- Prove2me | Theorems.Thm_PI_ZW_rightHalf_of
-- name    : PI.ZW.rightHalf_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:04.582203+00:00
-- url     : https://prove2.me/theorems/bbb37093-31f7-4827-85cf-97df41baee07
-- title:
--   ZW: right Half of
-- statement:
--   The ZW construction uses the right Half of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L81-L89

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

theorem PI.ZW.rightHalf_of (C₁ C₂ : ℝ) (h₁ : RightChiWith C₁) (h₂ : RightOneWith C₂) :
    RightHalfWith (max C₁ C₂) := by sorry
