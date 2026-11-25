-- Prove2me | Theorems.Thm_PI_QnRT_depthNumbers_threshold_eq
-- name    : PI.QnRT.depthNumbers_threshold_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:40:19.442863+00:00
-- url     : https://prove2.me/theorems/98937bb5-a0c1-410c-9524-ca4d50bc877a
-- title:
--   Qn RT: depth Numbers threshold eq
-- statement:
--   The Qn RT construction uses the depth Numbers threshold eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L130-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L130-L149

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}

theorem PI.QnRT.depthNumbers_threshold_eq (l : Fin r) : hpart2 (Hpk k r) (single (eI k r l) (eI k r l) 1) =
    dz l (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by sorry
