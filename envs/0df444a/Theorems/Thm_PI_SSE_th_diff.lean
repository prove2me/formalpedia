-- Prove2me | Theorems.Thm_PI_SSE_th_diff
-- name    : PI.SSE.th_diff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:21:21.525814+00:00
-- url     : https://prove2.me/theorems/59bb3e60-767d-426c-be83-4cd0864c80d5
-- title:
--   SSE: th diff
-- statement:
--   The SSE construction uses the th diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaA.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaA.lean#L58-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PI PI.SSE

theorem PI.SSE.th_diff (τ : ℂ) (hτ : 0 < τ.im) : Differentiable ℂ (th τ) := by sorry
