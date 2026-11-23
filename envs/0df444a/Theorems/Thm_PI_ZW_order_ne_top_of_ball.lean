-- Prove2me | Theorems.Thm_PI_ZW_order_ne_top_of_ball
-- name    : PI.ZW.order_ne_top_of_ball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:09.035323+00:00
-- url     : https://prove2.me/theorems/15ddd200-4a28-473d-a52b-eae93bcd36ba
-- title:
--   ZW: order ne top of ball
-- statement:
--   The ZW construction uses the order ne top of ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Jensen.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Jensen.lean#L9-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Jensen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric
open PI PI.ZW

theorem PI.ZW.order_ne_top_of_ball {f : ℂ → ℂ} {c z : ℂ} {R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : f c ≠ 0) (hz : z ∈ closedBall c R) : analyticOrderAt f z ≠ ⊤ := by sorry
