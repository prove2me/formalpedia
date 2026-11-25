-- Prove2me | Theorems.Thm_PI_HwUniqW_fix_of_smul
-- name    : PI.HwUniqW.fix_of_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:29.389803+00:00
-- url     : https://prove2.me/theorems/210089b8-4595-56e8-9f2b-81506a541783
-- title:
--   Hw Uniq W: fix of smul
-- statement:
--   The Hw Uniq W construction uses the fix of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L56-L59

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

theorem PI.HwUniqW.fix_of_smul {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {s : ℂ} (hs : s ≠ 0)
    {w : Fin (2 * r + k + 1) → ℂ} (h : m *ᵥ (s • w) = s • w) : m *ᵥ w = w := by sorry
