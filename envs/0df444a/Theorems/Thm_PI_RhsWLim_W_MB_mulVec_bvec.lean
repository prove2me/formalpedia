-- Prove2me | Theorems.Thm_PI_RhsWLim_W_MB_mulVec_bvec
-- name    : PI.RhsWLim.W.MB.mulVec_bvec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:27:24.121274+00:00
-- url     : https://prove2.me/theorems/1194cb8c-a06b-5bb0-8fc4-247137d07141
-- title:
--   MB: mul Vec bvec
-- statement:
--   The MB construction uses the mul Vec bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/MBaseMem.lean#L254-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/MBaseMem.lean#L254-L255

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

theorem PI.RhsWLim.W.MB.mulVec_bvec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j l : Fin n) : (A *ᵥ bvec j) l = A l j := by sorry
