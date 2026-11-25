-- Prove2me | Theorems.Thm_PI_RhsWLim_W_boost_mem
-- name    : PI.RhsWLim.W.boost_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:52.358081+00:00
-- url     : https://prove2.me/theorems/2eb75bb4-12a6-4f2d-8f15-721ad6086ce4
-- title:
--   W: boost mem
-- statement:
--   The W construction uses the boost mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/TransW.lean#L35-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/TransW.lean#L35-L102

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TransW
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
open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}

theorem PI.RhsWLim.W.boost_mem (y : Fin k → ℂ) (c : ℂ)
    (hS : ∑ l, conj (y l) * y l = ((‖c‖ : ℝ) : ℂ) ^ 2 - 1) (hc0 : c ≠ 0) :
    (boost y c)ᴴ * Hb k * boost y c = Hb k := by sorry
