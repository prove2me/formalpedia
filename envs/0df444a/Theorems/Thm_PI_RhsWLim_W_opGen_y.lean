-- Prove2me | Theorems.Thm_PI_RhsWLim_W_opGen_y
-- name    : PI.RhsWLim.W.opGen_y
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:13.488592+00:00
-- url     : https://prove2.me/theorems/95dd7156-9064-576f-94cf-c52a52ece1b0
-- title:
--   W: op Gen y
-- statement:
--   The W construction uses the op Gen y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L63-L65

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

theorem PI.RhsWLim.W.opGen_y (q : TrE k) (a : Fin k) :
    opGen k r q (wI k r a.castSucc) (wI k r (Fin.last k)) = opBeta k q a := by sorry
