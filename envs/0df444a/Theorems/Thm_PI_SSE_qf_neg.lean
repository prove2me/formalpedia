-- Prove2me | Theorems.Thm_PI_SSE_qf_neg
-- name    : PI.SSE.qf_neg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:21:12.894842+00:00
-- url     : https://prove2.me/theorems/d87b6660-0bf2-54d7-8b18-03b9ef52812b
-- title:
--   SSE: qf neg
-- statement:
--   The SSE construction uses the qf neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/LatExt.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/LatExt.lean#L21-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_LatExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Classical
open PI PI.SSE

theorem PI.SSE.qf_neg (A ω z : ℂ) (hA : A ≠ 0) : qf A ω (z + -ω) * qf A (-ω) z = 1 := by sorry
