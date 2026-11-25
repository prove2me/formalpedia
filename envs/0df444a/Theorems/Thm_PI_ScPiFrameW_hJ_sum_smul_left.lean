-- Prove2me | Theorems.Thm_PI_ScPiFrameW_hJ_sum_smul_left
-- name    : PI.ScPiFrameW.hJ_sum_smul_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:19.976292+00:00
-- url     : https://prove2.me/theorems/c8b2a205-bd20-4366-9ca0-b1c80139d27e
-- title:
--   Sc Pi Frame W: h J sum smul left
-- statement:
--   The Sc Pi Frame W construction uses the h J sum smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L53-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}

theorem PI.ScPiFrameW.hJ_sum_smul_left (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (g : ι → ℂ)
    (m : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a, g a • m a) y = ∑ a, star (g a) * hJ ε (m a) y := by sorry
