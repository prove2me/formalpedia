-- Prove2me | Theorems.Thm_PI_RhsWLim_W_opGen_c
-- name    : PI.RhsWLim.W.opGen_c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:53.32881+00:00
-- url     : https://prove2.me/theorems/2ed677ed-b32c-5a5e-9819-99d67bcc7f59
-- title:
--   W: op Gen c
-- statement:
--   The W construction uses the op Gen c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L67-L69

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

theorem PI.RhsWLim.W.opGen_c (q : TrE k) :
    opGen k r q (wI k r (Fin.last k)) (wI k r (Fin.last k)) = (q none : ℂ) * Complex.I := by sorry
