-- Prove2me | Theorems.Thm_PI_FglChordFactor_Wk_fix_unique
-- name    : PI.FglChordFactor.Wk.fix_unique
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:19.161609+00:00
-- url     : https://prove2.me/theorems/a2975ee4-6504-4583-be04-241792492cea
-- title:
--   Wk: fix unique
-- statement:
--   The Wk construction uses the fix unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/DerivativeFlog.lean#L68-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/DerivativeFlog.lean#L68-L81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS)
variable {p : ℕ} [Fact p.Prime]

theorem PI.FglChordFactor.Wk.fix_unique {a₁ a₂ a₃ a₄ a₆ : ℂ_[p]} {t V₁ V₂ : PowerSeries ℂ_[p]} (ht : PowerSeries.constantCoeff t = 0)
    (h₁ : V₁ = 1 + cP a₁ * t * V₁ + cP a₂ * t ^ 2 * V₁ + cP a₃ * t ^ 3 * V₁ ^ 2 + cP a₄ * t ^ 4 * V₁ ^ 2 +
      cP a₆ * t ^ 6 * V₁ ^ 3)
    (h₂ : V₂ = 1 + cP a₁ * t * V₂ + cP a₂ * t ^ 2 * V₂ + cP a₃ * t ^ 3 * V₂ ^ 2 + cP a₄ * t ^ 4 * V₂ ^ 2 +
      cP a₆ * t ^ 6 * V₂ ^ 3) : V₁ = V₂ := by sorry
