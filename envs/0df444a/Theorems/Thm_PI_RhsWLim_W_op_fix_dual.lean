-- Prove2me | Theorems.Thm_PI_RhsWLim_W_op_fix_dual
-- name    : PI.RhsWLim.W.op_fix_dual
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:55.805811+00:00
-- url     : https://prove2.me/theorems/a816898b-623e-535d-9c3d-89164e86430f
-- title:
--   W: op fix dual
-- statement:
--   The W construction uses the op fix dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushI.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushI.lean#L48-L53

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

theorem PI.RhsWLim.W.op_fix_dual {g : Mat k r} (hg : g ∈ UH (Hpk k r)) {f : Fin (2 * r + k + 1) → ℂ} (hf : g *ᵥ f = f) :
    gᴴ *ᵥ (Hpk k r *ᵥ f) = Hpk k r *ᵥ f := by sorry
