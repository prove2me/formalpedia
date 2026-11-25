-- Prove2me | Theorems.Thm_PI_ScPiFrameW_hJ_conj
-- name    : PI.ScPiFrameW.hJ_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:56:22.598786+00:00
-- url     : https://prove2.me/theorems/f5f9dee6-d916-4997-a1f0-162e8787d6da
-- title:
--   Sc Pi Frame W: h J conj
-- statement:
--   The Sc Pi Frame W construction uses the h J conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L23-L26

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

theorem PI.ScPiFrameW.hJ_conj (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by sorry
