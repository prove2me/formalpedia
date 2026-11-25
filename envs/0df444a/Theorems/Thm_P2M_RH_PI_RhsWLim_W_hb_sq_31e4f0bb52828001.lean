-- Prove2me | Theorems.Thm_P2M_RH_PI_RhsWLim_W_hb_sq_31e4f0bb52828001
-- name    : P2M_RH_PI_RhsWLim_W_hb_sq_31e4f0bb52828001
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:52:20.295405+00:00
-- url     : https://prove2.me/theorems/1d203142-549c-45ac-b9a6-7d95b5fd4024
-- title:
--   P2 M RH PI Rhs WLim W hb sq 31e4f0bb52828001: P2 M RH PI Rhs WLim W hb sq 31e4f0bb52828001
-- statement:
--   The P2 M RH PI Rhs WLim W hb sq 31e4f0bb52828001 construction uses the P2 M RH PI Rhs WLim W hb sq 31e4f0bb52828001 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushI.lean#L165-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushI.lean#L165-L171

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

theorem P2M_RH_PI_RhsWLim_W_hb_sq_31e4f0bb52828001 : Hb k * Hb k = 1 := by sorry

alias «PI».«RhsWLim».«W».«hb_sq» := P2M_RH_PI_RhsWLim_W_hb_sq_31e4f0bb52828001
