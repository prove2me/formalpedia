-- Prove2me | Theorems.Thm_PI_RhsWLim_W_lintegral_inv_smul
-- name    : PI.RhsWLim.W.lintegral_inv_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:42.223935+00:00
-- url     : https://prove2.me/theorems/0ce3dba3-afe9-4f50-9dfa-8546082e8677
-- title:
--   W: lintegral inv smul
-- statement:
--   The W construction uses the lintegral inv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushM.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushM.lean#L19-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushM
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

theorem PI.RhsWLim.W.lintegral_inv_smul {t : ℝ} (ht : 0 < t) {G : (Fin k → ℂ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G (t⁻¹ • y) = ENNReal.ofReal (t ^ Module.finrank ℝ (Fin k → ℂ)) * ∫⁻ y, G y := by sorry
