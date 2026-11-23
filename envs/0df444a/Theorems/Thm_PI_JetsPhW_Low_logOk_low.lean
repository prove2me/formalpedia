-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_logOk_low
-- name    : PI.JetsPhW.Low.logOk_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:59.254797+00:00
-- url     : https://prove2.me/theorems/3fffab9b-2d12-4ee2-b553-de08c60a9e2d
-- title:
--   Low: log Ok low
-- statement:
--   The Low construction uses the log Ok low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/FirstJetIntegralGeneralHolds.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/FirstJetIntegralGeneralHolds.lean#L12-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_FirstJetIntegralGeneralHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
open PI.JetsPhW

theorem PI.JetsPhW.Low.logOk_low {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (h : LogOk l ex) :
    PowerSeries.constantCoeff l = 0 ∧
      PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 ∧ ‖PowerSeries.coeff 1 ex‖ ≤ 1 := by sorry
