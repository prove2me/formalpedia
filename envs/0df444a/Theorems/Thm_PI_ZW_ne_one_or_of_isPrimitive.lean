-- Prove2me | Theorems.Thm_PI_ZW_ne_one_or_of_isPrimitive
-- name    : PI.ZW.ne_one_or_of_isPrimitive
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:32.459792+00:00
-- url     : https://prove2.me/theorems/1337d96d-e879-5468-8919-69b1d9eaae32
-- title:
--   ZW: ne one or of is Primitive
-- statement:
--   The ZW construction uses the ne one or of is Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L19-L25

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

theorem PI.ZW.ne_one_or_of_isPrimitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ ≠ 1 ∨ N = 1 := by sorry
