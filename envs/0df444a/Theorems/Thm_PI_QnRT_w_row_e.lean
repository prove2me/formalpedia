-- Prove2me | Theorems.Thm_PI_QnRT_w_row_e
-- name    : PI.QnRT.w_row_e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:19:53.0768+00:00
-- url     : https://prove2.me/theorems/bb91260d-18f1-4583-8fea-ab4c6191f8b9
-- title:
--   Qn RT: w row e
-- statement:
--   The Qn RT construction uses the w row e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L87-L94

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

theorem PI.QnRT.w_row_e (l : Fin r) (a : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l a (eI k r l) q = if q = esI k r l then (star a)⁻¹ else 0 := by sorry
