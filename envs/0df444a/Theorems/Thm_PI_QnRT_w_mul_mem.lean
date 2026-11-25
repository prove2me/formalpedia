-- Prove2me | Theorems.Thm_PI_QnRT_w_mul_mem
-- name    : PI.QnRT.w_mul_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:19:04.503955+00:00
-- url     : https://prove2.me/theorems/c19e3fdc-ac63-55fb-b98a-ca01a0015077
-- title:
--   Qn RT: w mul mem
-- statement:
--   The Qn RT construction uses the w mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L222-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L222-L249

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

theorem PI.QnRT.w_mul_mem (l : Fin r) (a : ℂ) (ha : a ≠ 0) (g₁ : Mx k r) (hg : g₁ ∈ Glev k r l.succ) :
    w1 k r l a * g₁ ∈ Glev k r l.castSucc := by sorry
