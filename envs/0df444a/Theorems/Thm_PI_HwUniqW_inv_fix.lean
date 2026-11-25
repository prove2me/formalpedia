-- Prove2me | Theorems.Thm_PI_HwUniqW_inv_fix
-- name    : PI.HwUniqW.inv_fix
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:37:46.609406+00:00
-- url     : https://prove2.me/theorems/322529da-e052-469e-b933-6d536797f870
-- title:
--   Hw Uniq W: inv fix
-- statement:
--   The Hw Uniq W construction uses the inv fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L43-L46

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

theorem PI.HwUniqW.inv_fix {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : a ∈ UH (Hpk k r))
    {v : Fin (2 * r + k + 1) → ℂ} (hv : a *ᵥ v = v) : a⁻¹ *ᵥ v = v := by sorry
