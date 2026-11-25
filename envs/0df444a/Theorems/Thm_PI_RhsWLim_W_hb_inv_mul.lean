-- Prove2me | Theorems.Thm_PI_RhsWLim_W_hb_inv_mul
-- name    : PI.RhsWLim.W.hb_inv_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:49.517824+00:00
-- url     : https://prove2.me/theorems/da9edbcf-9f8c-59f6-b9e3-fb7e588793a6
-- title:
--   W: hb inv mul
-- statement:
--   The W construction uses the hb inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushI.lean#L173-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushI.lean#L173-L176

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim PI.RhsWLim.W.MB
variable {k r : ℕ}

theorem PI.RhsWLim.W.hb_inv_mul {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) :
    (Hb k * μᴴ * Hb k) * μ = 1 := by sorry
