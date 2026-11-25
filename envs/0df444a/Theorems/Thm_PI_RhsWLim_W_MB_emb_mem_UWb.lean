-- Prove2me | Theorems.Thm_PI_RhsWLim_W_MB_emb_mem_UWb
-- name    : PI.RhsWLim.W.MB.emb_mem_UWb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:26:23.260993+00:00
-- url     : https://prove2.me/theorems/6e6db3cc-cd2a-5472-8be6-6d012152657a
-- title:
--   MB: emb mem UWb
-- statement:
--   The MB construction uses the emb mem UWb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/MBaseMem.lean#L265-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/MBaseMem.lean#L265-L273

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

theorem PI.RhsWLim.W.MB.emb_mem_UWb {a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (ha : aᴴ * Hb k * a = Hb k) :
    embWb k r a ∈ UWb k r := by sorry
