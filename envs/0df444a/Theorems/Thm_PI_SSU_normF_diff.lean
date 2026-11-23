-- Prove2me | Theorems.Thm_PI_SSU_normF_diff
-- name    : PI.SSU.normF_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:42.78781+00:00
-- url     : https://prove2.me/theorems/8a52e2b5-8c59-4300-ae99-2fe43165d5f7
-- title:
--   SSU: norm F diff
-- statement:
--   The SSU construction uses the norm F diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesUniqueness/ZeroOfCoef.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesUniqueness/ZeroOfCoef.lean#L51-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_Complete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_ZeroOfCoef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SSU
open Complex

theorem PI.SSU.normF_diff (a A l : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Differentiable ℂ (normF a A l F) := by sorry
