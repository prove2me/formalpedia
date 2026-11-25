-- Prove2me | Theorems.Thm_PI_HwUniqW_frame_inv_mulVec_negativeVector
-- name    : PI.HwUniqW.frame_inv_mulVec_negativeVector
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:37:40.901124+00:00
-- url     : https://prove2.me/theorems/a14752e7-d652-46e0-b079-4044ce89bda2
-- title:
--   Hw Uniq W: frame inv mul Vec negative Vector
-- statement:
--   The Hw Uniq W construction uses the frame inv mul Vec negative Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L48-L54

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

theorem PI.HwUniqW.frame_inv_mulVec_negativeVector {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) :
    g⁻¹ *ᵥ z = (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) := by sorry
