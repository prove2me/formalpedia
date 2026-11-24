-- Prove2me | Theorems.Thm_PI_ScPiFrameW_exists_rel
-- name    : PI.ScPiFrameW.exists_rel
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:30.441533+00:00
-- url     : https://prove2.me/theorems/abaf2a36-9583-4112-9390-15a15222bf38
-- title:
--   Sc Pi Frame W: exists rel
-- statement:
--   The Sc Pi Frame W construction uses the exists rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L73-L79

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

theorem PI.ScPiFrameW.exists_rel {ι κ : Type*} [Fintype ι] [Fintype κ] (v : κ → ι → ℂ)
    (h : Fintype.card ι < Fintype.card κ) : ∃ g : κ → ℂ, ∑ j, g j • v j = 0 ∧ ∃ j, g j ≠ 0 := by sorry
