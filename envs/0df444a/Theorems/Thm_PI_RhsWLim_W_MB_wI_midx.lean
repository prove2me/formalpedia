-- Prove2me | Theorems.Thm_PI_RhsWLim_W_MB_wI_midx
-- name    : PI.RhsWLim.W.MB.wI_midx
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:27:44.654205+00:00
-- url     : https://prove2.me/theorems/9572e3fd-0883-4a71-bd36-3a8a11ef73f5
-- title:
--   MB: w I midx
-- statement:
--   The MB construction uses the w I midx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/MBaseMem.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/MBaseMem.lean#L27-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.MB
open PI.RhsWLim
variable {k r : ℕ}

theorem PI.RhsWLim.W.MB.wI_midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : wI k r (midx hi) = i := by sorry
