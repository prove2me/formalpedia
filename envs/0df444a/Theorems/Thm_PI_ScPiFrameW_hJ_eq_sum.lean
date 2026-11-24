-- Prove2me | Theorems.Thm_PI_ScPiFrameW_hJ_eq_sum
-- name    : PI.ScPiFrameW.hJ_eq_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:54:38.312921+00:00
-- url     : https://prove2.me/theorems/a025f614-0db3-407f-b0b1-9f39dd587df6
-- title:
--   Sc Pi Frame W: h J eq sum
-- statement:
--   The Sc Pi Frame W construction uses the h J eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L19-L21

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

theorem PI.ScPiFrameW.hJ_eq_sum (ε : Fin n → Bool) (x y : Fin n → ℂ) :
    hJ ε x y = ∑ j, star (x j) * (sg ε j * y j) := by sorry
