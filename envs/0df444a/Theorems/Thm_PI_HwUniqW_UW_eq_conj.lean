-- Prove2me | Theorems.Thm_PI_HwUniqW_UW_eq_conj
-- name    : PI.HwUniqW.UW_eq_conj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:37:47.627783+00:00
-- url     : https://prove2.me/theorems/102e3b8d-0233-4938-ac29-39ef59ac9c1d
-- title:
--   Hw Uniq W: UW eq conj
-- statement:
--   The Hw Uniq W construction uses the UW eq conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L102-L109

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

theorem PI.HwUniqW.UW_eq_conj {z : Fin (2 * r + k + 1) → ℂ} {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hT : 0 < Tz k r z) (hg : IsFrameW k r z g) (hx : x ∈ UWset k r z) :
    ∃ h ∈ UJset (allPos k), g⁻¹ * x * g = blockW k r h ∧ x = g * blockW k r h * g⁻¹ := by sorry
