-- Prove2me | Theorems.Thm_PI_QnRT_exp_diag2
-- name    : PI.QnRT.exp_diag2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:21:46.996877+00:00
-- url     : https://prove2.me/theorems/07c77f3d-cf18-52e7-b6f3-06a830670afb
-- title:
--   Qn RT: exp diag2
-- statement:
--   The Qn RT construction uses the exp diag2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L337-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L337-L349

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}

theorem PI.QnRT.exp_diag2 (l : Fin r) (x y : ℂ) :
    NormedSpace.exp (diagonal (fun p => if p = eI k r l then x else if p = esI k r l then y else 0) : Mx k r) =
      dg l (Complex.exp x) (Complex.exp y) := by sorry
