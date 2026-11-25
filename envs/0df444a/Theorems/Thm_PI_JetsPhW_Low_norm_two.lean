-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_norm_two
-- name    : PI.JetsPhW.Low.norm_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:11:11.854403+00:00
-- url     : https://prove2.me/theorems/2f698bea-8b35-4474-b13d-ec903d51e695
-- title:
--   Low: norm two
-- statement:
--   The Low construction uses the norm two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/ExpLow.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/ExpLow.lean#L28-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLow
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
variable {p : ℕ} [Fact p.Prime]

theorem PI.JetsPhW.Low.norm_two (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by sorry
