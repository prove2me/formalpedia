-- Prove2me | Theorems.Thm_PI_ScPiFrameW_frame_hypotheses_rank_zero
-- name    : PI.ScPiFrameW.frame_hypotheses_rank_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:43.245807+00:00
-- url     : https://prove2.me/theorems/eb0c4d19-9c7a-49c2-b806-2d861dcb3bb2
-- title:
--   Sc Pi Frame W: frame hypotheses rank zero
-- statement:
--   The Sc Pi Frame W construction uses the frame hypotheses rank zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/FrameHypothesesRankZero.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/FrameHypothesesRankZero.lean#L32-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameHypothesesRankZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ScPiFrameW
open PI.ScPiExists

theorem PI.ScPiFrameW.frame_hypotheses_rank_zero :
    let ε : Fin 2 → Bool := ![true, false]
    let z : Fin 2 → ℂ := ![0, 1]
    (2 = 2 * 0 + 1 + 1) ∧
    (∀ i : Fin 2, ε i = if i.val < 1 - 1 then true else decide ((i.val - (1 - 1)) % 2 = 0)) ∧
    hJ ε z z = -((1 : ℝ) : ℂ) := by sorry
