-- Prove2me | Theorems.Thm_PI_SSE_term_pos
-- name    : PI.SSE.term_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:20:16.510061+00:00
-- url     : https://prove2.me/theorems/39f3e429-eab4-4b7c-b9f9-82cb67e4e731
-- title:
--   SSE: term pos
-- statement:
--   The SSE construction uses the term pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L12-L20

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

theorem PI.SSE.term_pos (τ : ℂ) (n : ℕ) :
    jacobiTheta₂'_term (n : ℤ) (1 / 2 + τ / 2) τ
      = 2 * Real.pi * I * (n : ℂ) * ((-1) ^ n * qe τ n) := by sorry
