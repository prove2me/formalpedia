-- Prove2me | Theorems.Thm_PI_ZW_log_mul_abs_add_two_nonneg
-- name    : PI.ZW.log_mul_abs_add_two_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:33.015742+00:00
-- url     : https://prove2.me/theorems/eb4d8974-8464-59d5-8442-a71bb01d65f0
-- title:
--   ZW: log mul abs add two nonneg
-- statement:
--   The ZW construction uses the log mul abs add two nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L27-L30

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

theorem PI.ZW.log_mul_abs_add_two_nonneg (N : ℕ) [NeZero N] (t : ℝ) : 0 ≤ Real.log (N * (|t| + 2)) := by sorry
