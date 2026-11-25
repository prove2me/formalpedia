-- Prove2me | Theorems.Thm_PI_RhsWLim_W_HU_inc_memb
-- name    : PI.RhsWLim.W.HU.inc_memb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:27:17.639652+00:00
-- url     : https://prove2.me/theorems/37896de6-21a7-5b67-800e-8726ecdb627a
-- title:
--   HU: inc memb
-- statement:
--   The HU construction uses the inc memb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L161-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L161-L162

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

theorem PI.RhsWLim.W.HU.inc_memb : MeasurableEmbedding (inc : Gp k r → Mt k r) := by sorry
