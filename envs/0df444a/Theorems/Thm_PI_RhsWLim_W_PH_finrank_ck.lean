-- Prove2me | Theorems.Thm_PI_RhsWLim_W_PH_finrank_ck
-- name    : PI.RhsWLim.W.PH.finrank_ck
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:07.029478+00:00
-- url     : https://prove2.me/theorems/8b76279d-ed79-4e9a-ae68-4fdebd624ed0
-- title:
--   PH: finrank ck
-- statement:
--   The PH construction uses the finrank ck property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PolarHyp.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PolarHyp.lean#L39-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp
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
open MeasureTheory Filter Topology Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.PH

theorem PI.RhsWLim.W.PH.finrank_ck (k : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Fin k)) = 2 * k := by sorry
