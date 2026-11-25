-- Prove2me | Theorems.Thm_PI_SSE_I_eq
-- name    : PI.SSE.I_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:29.000921+00:00
-- url     : https://prove2.me/theorems/4cc11912-83fd-4563-8af9-a1ea4e430177
-- title:
--   SSE: I eq
-- statement:
--   The SSE construction uses the I eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/GenEqOf.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/GenEqOf.lean#L27-L38

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

theorem PI.SSE.I_eq (v₁ v₂ : ℂ) (h : ((starRingEnd ℂ) v₁ * v₂).im ≠ 0) :
    I = ((starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂) /
      (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ)) := by sorry
