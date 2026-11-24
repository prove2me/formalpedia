-- Prove2me | Theorems.Thm_PI_ScPiFrameW_hJ_self
-- name    : PI.ScPiFrameW.hJ_self
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:53.110706+00:00
-- url     : https://prove2.me/theorems/8a35a1c0-e44d-4a51-a768-4edc94974a99
-- title:
--   Sc Pi Frame W: h J self
-- statement:
--   The Sc Pi Frame W construction uses the h J self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L61-L67

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

theorem PI.ScPiFrameW.hJ_self (ε : Fin n → Bool) (x : Fin n → ℂ) :
    hJ ε x x = ((∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (x j) : ℝ) : ℂ) := by sorry
