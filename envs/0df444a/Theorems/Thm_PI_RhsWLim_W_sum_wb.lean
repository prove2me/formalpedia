-- Prove2me | Theorems.Thm_PI_RhsWLim_W_sum_wb
-- name    : PI.RhsWLim.W.sum_wb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:55.011162+00:00
-- url     : https://prove2.me/theorems/6bd165ac-da36-59e1-bdd1-05a64a4638d7
-- title:
--   W: sum wb
-- statement:
--   The W construction uses the sum wb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsTest.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsTest.lean#L25-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}

theorem PI.RhsWLim.W.sum_wb (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by sorry
