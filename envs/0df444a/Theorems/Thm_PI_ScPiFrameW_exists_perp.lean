-- Prove2me | Theorems.Thm_PI_ScPiFrameW_exists_perp
-- name    : PI.ScPiFrameW.exists_perp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:49.289803+00:00
-- url     : https://prove2.me/theorems/4d2ec62e-93c6-420b-824a-7578cf5df840
-- title:
--   Sc Pi Frame W: exists perp
-- statement:
--   The Sc Pi Frame W construction uses the exists perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L81-L89

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

theorem PI.ScPiFrameW.exists_perp (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (u : ι → Fin n → ℂ)
    (h : Fintype.card ι < n) : ∃ y : Fin n → ℂ, y ≠ 0 ∧ ∀ i, hJ ε (u i) y = 0 := by sorry
