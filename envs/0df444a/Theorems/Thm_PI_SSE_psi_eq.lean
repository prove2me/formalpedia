-- Prove2me | Theorems.Thm_PI_SSE_psi_eq
-- name    : PI.SSE.psi_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:23:54.630985+00:00
-- url     : https://prove2.me/theorems/ab405945-1420-4582-ad2f-764468c591c5
-- title:
--   SSE: psi eq
-- statement:
--   The SSE construction uses the psi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/LatExt.lean#L107-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/LatExt.lean#L107-L132

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

theorem PI.SSE.psi_eq (v₁ v₂ : ℂ) (h : ((starRingEnd ℂ) v₁ * v₂).im ≠ 0) (m n : ℤ) :
    (-1 : ℂ) ^ (m + n + m * n) =
      if ((m : ℂ) * v₁ + n * v₂) / 2 ∈ PI.lat2 v₁ v₂ then 1 else -1 := by sorry
