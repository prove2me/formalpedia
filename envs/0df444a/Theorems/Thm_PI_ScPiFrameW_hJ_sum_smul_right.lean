-- Prove2me | Theorems.Thm_PI_ScPiFrameW_hJ_sum_smul_right
-- name    : PI.ScPiFrameW.hJ_sum_smul_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:18.253255+00:00
-- url     : https://prove2.me/theorems/7aa976e8-fa68-549f-b5ae-f381e18f48e1
-- title:
--   Sc Pi Frame W: h J sum smul right
-- statement:
--   The Sc Pi Frame W construction uses the h J sum smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L46-L51

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

theorem PI.ScPiFrameW.hJ_sum_smul_right (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (g : ι → ℂ)
    (m : ι → Fin n → ℂ) (x : Fin n → ℂ) :
    hJ ε x (∑ b, g b • m b) = ∑ b, g b * hJ ε x (m b) := by sorry
