-- Prove2me | Theorems.Thm_PI_QnRT_w_col_es
-- name    : PI.QnRT.w_col_es
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:44:51.122001+00:00
-- url     : https://prove2.me/theorems/06e500db-efa5-487d-8022-8b1dc88a6884
-- title:
--   Qn RT: w col es
-- statement:
--   The Qn RT construction uses the w col es property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L70-L77

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

theorem PI.QnRT.w_col_es (l : Fin r) (a : ℂ) (s : Fin (2 * r + k + 1)) :
    w1 k r l a s (esI k r l) = if s = eI k r l then (star a)⁻¹ else 0 := by sorry
