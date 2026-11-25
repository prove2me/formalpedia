-- Prove2me | Theorems.Thm_PI_ScPiFrameW_hJ_smul_right
-- name    : PI.ScPiFrameW.hJ_smul_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:02.40121+00:00
-- url     : https://prove2.me/theorems/05b49885-26aa-4491-8277-e98735cd02f3
-- title:
--   Sc Pi Frame W: h J smul right
-- statement:
--   The Sc Pi Frame W construction uses the h J smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L41-L44

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

theorem PI.ScPiFrameW.hJ_smul_right (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    hJ ε x (c • y) = c * hJ ε x y := by sorry
