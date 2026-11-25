-- Prove2me | Theorems.Thm_PI_RhsWLim_W_op_uwb_col
-- name    : PI.RhsWLim.W.op_uwb_col
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:52:02.583975+00:00
-- url     : https://prove2.me/theorems/8779d9e9-fc76-5dac-9fe8-82400a1548ff
-- title:
--   W: op uwb col
-- statement:
--   The W construction uses the op uwb col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushI.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushI.lean#L55-L59

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

theorem PI.RhsWLim.W.op_uwb_col {g : Mat k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g l i = if l = i then 1 else 0 := by sorry
