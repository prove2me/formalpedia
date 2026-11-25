-- Prove2me | Theorems.Thm_PI_RhsWLim_W_mulVec_base
-- name    : PI.RhsWLim.W.mulVec_base
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:05.330247+00:00
-- url     : https://prove2.me/theorems/bd1b7c3a-9ed6-4f16-9a6b-53638ec12d95
-- title:
--   W: mul Vec base
-- statement:
--   The W construction uses the mul Vec base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L59-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {k r : ℕ}

theorem PI.RhsWLim.W.mulVec_base (T' : ℝ) (M : Mat k r) (i : Fin (2 * r + k + 1)) :
    (M *ᵥ opBase k r T') i = (Real.sqrt T' : ℂ) * M i (wI k r (Fin.last k)) := by sorry
