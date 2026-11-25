-- Prove2me | Theorems.Thm_PI_ScPiFrameW_frame_hypotheses_rank_one
-- name    : PI.ScPiFrameW.frame_hypotheses_rank_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:08.095958+00:00
-- url     : https://prove2.me/theorems/c5d2f09b-ba07-477b-a93f-91e6af80ecbb
-- title:
--   Sc Pi Frame W: frame hypotheses rank one
-- statement:
--   The Sc Pi Frame W construction uses the frame hypotheses rank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/FrameHypothesesRankZero.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/FrameHypothesesRankZero.lean#L11-L30

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

theorem PI.ScPiFrameW.frame_hypotheses_rank_one :
    let ε : Fin 4 → Bool := ![true, false, true, false]
    let e : Fin 1 → Fin 4 → ℂ := fun _ => ![1, 1, 0, 0]
    let f : Fin 1 → Fin 4 → ℂ := fun _ => ![1 / 2, -1 / 2, 0, 0]
    let z : Fin 4 → ℂ := ![0, 0, 0, 1]
    (4 = 2 * 1 + 1 + 1) ∧
    (∀ i : Fin 4, ε i = if i.val < 1 - 1 then true else decide ((i.val - (1 - 1)) % 2 = 0)) ∧
    (∀ a b, hJ ε (e a) (e b) = 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
    (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧
    (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) ∧ hJ ε z z = -((1 : ℝ) : ℂ) := by sorry
