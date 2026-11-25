-- Prove2me | Theorems.Thm_PI_ScPiFrameW_hJ_self_re
-- name    : PI.ScPiFrameW.hJ_self_re
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:13.775618+00:00
-- url     : https://prove2.me/theorems/be0dd805-268a-4eec-8f48-919db0052cdf
-- title:
--   Sc Pi Frame W: h J self re
-- statement:
--   The Sc Pi Frame W construction uses the h J self re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L69-L71

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

theorem PI.ScPiFrameW.hJ_self_re (ε : Fin n → Bool) (x : Fin n → ℂ) :
    (hJ ε x x).re = ∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (x j) := by sorry
