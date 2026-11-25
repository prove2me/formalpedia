-- Prove2me | Theorems.Thm_PI_SSE_expo1
-- name    : PI.SSE.expo1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:02.166986+00:00
-- url     : https://prove2.me/theorems/90bf9feb-61a6-586c-b056-85681898fdeb
-- title:
--   SSE: expo1
-- statement:
--   The SSE construction uses the expo1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/GenEqOf.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/GenEqOf.lean#L12-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_GenEqOf
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

theorem PI.SSE.expo1 (v₁ p₁ A z : ℂ) (hv₁ : v₁ ≠ 0) (hA : A ≠ 0) :
    Real.pi * p₁ / (2 * A * v₁) * (z + v₁) ^ 2 =
      Real.pi * p₁ * (z + v₁ / 2) / A + Real.pi * p₁ / (2 * A * v₁) * z ^ 2 := by sorry
