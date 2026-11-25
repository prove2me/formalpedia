-- Prove2me | Theorems.Thm_PI_ScPiFrameW_hJ_smul_left
-- name    : PI.ScPiFrameW.hJ_smul_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:10.451687+00:00
-- url     : https://prove2.me/theorems/6503e5ec-dd1d-4d8f-9f8a-5e980dac2da5
-- title:
--   Sc Pi Frame W: h J smul left
-- statement:
--   The Sc Pi Frame W construction uses the h J smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L36-L39

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

theorem PI.ScPiFrameW.hJ_smul_left (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    hJ ε (c • x) y = star c * hJ ε x y := by sorry
