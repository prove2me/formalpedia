-- Prove2me | Theorems.Thm_PI_ScPiFrameW_hJ_sub_right
-- name    : PI.ScPiFrameW.hJ_sub_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:30.140006+00:00
-- url     : https://prove2.me/theorems/d07f6d0e-38a9-4bc1-8d8c-a7f55d1afab2
-- title:
--   Sc Pi Frame W: h J sub right
-- statement:
--   The Sc Pi Frame W construction uses the h J sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L32-L34

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

theorem PI.ScPiFrameW.hJ_sub_right (ε : Fin n → Bool) (x y y' : Fin n → ℂ) :
    hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by sorry
