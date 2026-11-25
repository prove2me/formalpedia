-- Prove2me | Theorems.Thm_PI_SSE_norm_succ_le
-- name    : PI.SSE.norm_succ_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:23:11.541312+00:00
-- url     : https://prove2.me/theorems/06ed2824-1588-55ba-b4cb-34da403ed4fb
-- title:
--   SSE: norm succ le
-- statement:
--   The SSE construction uses the norm succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L58-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L58-L80

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

theorem PI.SSE.norm_succ_le (τ : ℂ) (hy : 0 < τ.im) (n : ℕ) :
    ‖(2 * ((n + 1 : ℕ) : ℂ) + 1) * ((-1) ^ (n + 1) * qe τ (n + 1))‖
      ≤ (3 * Real.exp (-(2 * Real.pi * τ.im))) ^ (n + 1) := by sorry
