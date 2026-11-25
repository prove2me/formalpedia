-- Prove2me | Theorems.Thm_PI_Residue_pow_le_lower
-- name    : PI.Residue.pow_le_lower
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:17.364802+00:00
-- url     : https://prove2.me/theorems/a290c9c0-5c5e-43d1-b83e-2d28f5a60316
-- title:
--   Residue: pow le lower
-- statement:
--   The Residue construction uses the pow le lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/ThirdLeLog.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/ThirdLeLog.lean#L17-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_ThirdLeLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue

theorem PI.Residue.pow_le_lower (m : ℕ) (hm : 2 ≤ m) :
    (3 / 2 : ℝ) ^ m ≤ 4 / 9 * (3 * Real.pi / 4) ^ m := by sorry
