-- Prove2me | Theorems.Thm_PI_RhsWLim_W_phiT_coord_c
-- name    : PI.RhsWLim.W.phiT_coord_c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:07.348166+00:00
-- url     : https://prove2.me/theorems/0d2d6815-ab65-5f05-9248-8c48b2b9ea10
-- title:
--   W: phi T coord c
-- statement:
--   The W construction uses the phi T coord c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L121-L123

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

theorem PI.RhsWLim.W.phiT_coord_c (T' : ℝ) (q : TrE k) :
    phiT k r T' q none = (Complex.log (psiV k r T' q (wI k r (Fin.last k)))).im := by sorry
