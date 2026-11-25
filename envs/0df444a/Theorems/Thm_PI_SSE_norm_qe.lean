-- Prove2me | Theorems.Thm_PI_SSE_norm_qe
-- name    : PI.SSE.norm_qe
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:54.013209+00:00
-- url     : https://prove2.me/theorems/be4f51d8-3c46-47f8-995d-c8f502d4de7a
-- title:
--   SSE: norm qe
-- statement:
--   The SSE construction uses the norm qe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L47-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaNz
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

theorem PI.SSE.norm_qe (τ : ℂ) (n : ℕ) :
    ‖qe τ n‖ = Real.exp (-(Real.pi * τ.im * ((n : ℝ) * ((n : ℝ) + 1)))) := by sorry
