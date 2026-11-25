-- Prove2me | Theorems.Thm_PI_SSU_zero_of_coef
-- name    : PI.SSU.zero_of_coef
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:37:06.332564+00:00
-- url     : https://prove2.me/theorems/5d57d8d9-31ee-422f-ba97-eaf932163673
-- title:
--   SSU: zero of coef
-- statement:
--   The SSU construction uses the zero of coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesUniqueness/ZeroOfCoef.lean#L73-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesUniqueness/ZeroOfCoef.lean#L73-L91

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

theorem PI.SSU.zero_of_coef (hK : KeyP) (a b A p q : ℂ) (k : ℤ) (ha : a ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hk1 : k = 1 ∨ k = -1)
    (hk : (Real.pi : ℂ) / A * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
      -(2 * (Real.pi : ℂ) * I * k))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (hFa : FE A a p F) (hFb : FE A b q F)
    (h0 : coef (normF a A (Complex.log p) F) 0 = 0) : F = 0 := by sorry
