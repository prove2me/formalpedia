-- Prove2me | Theorems.Thm_PI_ZW_mem_closedBall_of_right
-- name    : PI.ZW.mem_closedBall_of_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:41.288066+00:00
-- url     : https://prove2.me/theorems/6d8757bf-09d0-465a-8085-1e670dc4d696
-- title:
--   ZW: mem closed Ball of right
-- statement:
--   The ZW construction uses the mem closed Ball of right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightChi.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightChi.lean#L21-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex
open PI PI.ZW

theorem PI.ZW.mem_closedBall_of_right {ρ : ℂ} {t : ℝ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) (h3 : |ρ.im - t| ≤ 1) :
    ρ ∈ closedBall (2 + t * I) (37 / 20) := by sorry
