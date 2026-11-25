-- Prove2me | Theorems.Thm_PI_SSE_small_of_im
-- name    : PI.SSE.small_of_im
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:20:34.500824+00:00
-- url     : https://prove2.me/theorems/26d8e239-d88e-4de7-84ca-6c2932791708
-- title:
--   SSE: small of im
-- statement:
--   The SSE construction uses the small of im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L82-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/ThetaNz.lean#L82-L91

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

theorem PI.SSE.small_of_im (y : ℝ) (hy : 0 < y) (h3 : 3 ≤ 4 * y ^ 2) :
    3 * Real.exp (-(2 * Real.pi * y)) < 1 / 2 := by sorry
