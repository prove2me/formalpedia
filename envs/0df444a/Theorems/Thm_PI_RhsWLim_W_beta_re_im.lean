-- Prove2me | Theorems.Thm_PI_RhsWLim_W_beta_re_im
-- name    : PI.RhsWLim.W.beta_re_im
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:50:47.534184+00:00
-- url     : https://prove2.me/theorems/83dacf9d-fbca-51a9-8512-5b2bf41ab513
-- title:
--   W: beta re im
-- statement:
--   The W construction uses the beta re im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L128-L136

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

theorem PI.RhsWLim.W.beta_re_im (T' : ℝ) (q : TrE k) (a : Fin k) :
    (Real.sqrt T' : ℂ) * opBeta k q a =
      ((Real.sqrt T' / Real.sqrt 2 * q (some (a, false)) : ℝ) : ℂ)
        + ((Real.sqrt T' / Real.sqrt 2 * q (some (a, true)) : ℝ) : ℂ) * Complex.I := by sorry
