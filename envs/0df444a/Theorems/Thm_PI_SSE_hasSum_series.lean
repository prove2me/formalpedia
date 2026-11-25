-- Prove2me | Theorems.Thm_PI_SSE_hasSum_series
-- name    : PI.SSE.hasSum_series
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:12.465999+00:00
-- url     : https://prove2.me/theorems/9dd5d75f-9985-47a1-9b31-5b5a605139a7
-- title:
--   SSE: has Sum series
-- statement:
--   The SSE construction uses the has Sum series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L38-L45

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

theorem PI.SSE.hasSum_series (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * Real.pi * I * ((2 * (n : ℂ) + 1) * ((-1) ^ n * qe τ n)))
      (jacobiTheta₂' (1 / 2 + τ / 2) τ) := by sorry
