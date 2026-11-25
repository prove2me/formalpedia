-- Prove2me | Theorems.Thm_PI_RhsWLim_W_testJ
-- name    : PI.RhsWLim.W.testJ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:35:13.87183+00:00
-- url     : https://prove2.me/theorems/714c113e-4694-52de-913d-094845c08726
-- title:
--   W: test J
-- statement:
--   The W construction uses the test J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/ConstCut.lean#L79-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/ConstCut.lean#L79-L138

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

theorem PI.RhsWLim.W.testJ (k : ℕ) (T T' : ℝ) (hTT : 0 < T * T') :
    0 < ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ∧
      ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ < ⊤ := by sorry
