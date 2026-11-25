-- Prove2me | Theorems.Thm_PI_RhsWLim_W_psiV_strict
-- name    : PI.RhsWLim.W.psiV_strict
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:50:49.375573+00:00
-- url     : https://prove2.me/theorems/477debd6-911c-5eae-9ca5-2a47035eafaa
-- title:
--   W: psi V strict
-- statement:
--   The W construction uses the psi V strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L77-L84

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

theorem PI.RhsWLim.W.psiV_strict (T' : ℝ) : HasStrictFDerivAt (psiV k r T')
    ((mvL k r (opBase k r T')).comp ((1 : Mat k r →L[ℝ] Mat k r).comp (opGenL k r))) 0 := by sorry
