-- Prove2me | Theorems.Thm_PI_RhsWLim_W_gauge_of_lim
-- name    : PI.RhsWLim.W.gauge_of_lim
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:58.02833+00:00
-- url     : https://prove2.me/theorems/84a1db32-9bc8-4801-abad-1659ad1875a5
-- title:
--   W: gauge of lim
-- statement:
--   The W construction uses the gauge of lim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/ConstCut.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/ConstCut.lean#L60-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
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

theorem PI.RhsWLim.W.gauge_of_lim {k r : ℕ} (νg : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) νg)
    (hL : ∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)) :
    IsGaugeOn k r (UWb k r) νg := by sorry
