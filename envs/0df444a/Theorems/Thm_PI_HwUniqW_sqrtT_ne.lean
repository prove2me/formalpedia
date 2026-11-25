-- Prove2me | Theorems.Thm_PI_HwUniqW_sqrtT_ne
-- name    : PI.HwUniqW.sqrtT_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:56.264235+00:00
-- url     : https://prove2.me/theorems/9ebf5493-8d62-460f-a5b8-51f5957e397e
-- title:
--   Hw Uniq W: sqrt T ne
-- statement:
--   The Hw Uniq W construction uses the sqrt T ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L61-L62

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}

theorem PI.HwUniqW.sqrtT_ne {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) :
    (((Real.sqrt (Tz k r z) : ℝ) : ℂ)) ≠ 0 := by sorry
