-- Prove2me | Theorems.Thm_PI_RhsWLim_W_HU_inc_mul
-- name    : PI.RhsWLim.W.HU.inc_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:28:41.895841+00:00
-- url     : https://prove2.me/theorems/f559f9b3-b1cb-433e-9dc6-5405dd090b07
-- title:
--   HU: inc mul
-- statement:
--   The HU construction uses the inc mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L188-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L188-L188

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU
open PI.RhsWLim
variable {k r : ℕ}

theorem PI.RhsWLim.W.HU.inc_mul (a b : Gp k r) : inc (a * b) = lmulM (Matrix.of (inc a)) (inc b) := by sorry
