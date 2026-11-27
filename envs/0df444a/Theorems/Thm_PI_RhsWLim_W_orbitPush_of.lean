-- Prove2me | Theorems.Thm_PI_RhsWLim_W_orbitPush_of
-- name    : PI.RhsWLim.W.orbitPush_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:23.082816+00:00
-- url     : https://prove2.me/theorems/0c35ed10-5f3a-5a10-8a65-193d5840ccc5
-- title:
--   W: orbit Push of
-- statement:
--   The W construction uses the orbit Push of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushCut.lean#L104-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushCut.lean#L104-L136

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
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

theorem PI.RhsWLim.W.orbitPush_of (h2 : GaugeVolUk) (hK : GaugeK) (hT : TubeLimK) (hI : HypInv) (hR : OrbRepY)
    (hL : HypLocal) (hE : OpEMeas) (hF : HypLF) : OrbitPush := by sorry
