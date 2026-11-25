-- Prove2me | Theorems.Thm_PI_RhsWLim_W_dpsi_apply
-- name    : PI.RhsWLim.W.dpsi_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:13.677441+00:00
-- url     : https://prove2.me/theorems/ba55ad49-eaf7-4640-8d66-c8852037ce1c
-- title:
--   W: dpsi apply
-- statement:
--   The W construction uses the dpsi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L86-L90

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

theorem PI.RhsWLim.W.dpsi_apply (T' : ℝ) (q : TrE k) (i : Fin (2 * r + k + 1)) :
    ((mvL k r (opBase k r T')).comp ((1 : Mat k r →L[ℝ] Mat k r).comp (opGenL k r))) q i
      = (Real.sqrt T' : ℂ) * opGen k r q i (wI k r (Fin.last k)) := by sorry
