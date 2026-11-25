-- Prove2me | Theorems.Thm_PI_RhsWLim_W_coneSh_eq
-- name    : PI.RhsWLim.W.coneSh_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:00.646261+00:00
-- url     : https://prove2.me/theorems/a6912b3d-93e4-5816-80ba-e2eb279ef03c
-- title:
--   W: cone Sh eq
-- statement:
--   The W construction uses the cone Sh eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushV.lean#L38-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushV.lean#L38-L63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
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
open PI.RhsWLim
variable {k : ℕ}

theorem PI.RhsWLim.W.coneSh_eq {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) :
    coneSh k T' E = {p | qf k p < 0 ∧ 1 < tau k T' p ∧ tau k T' p < 2 ∧ (tau k T' p)⁻¹ • p ∈ E} := by sorry
