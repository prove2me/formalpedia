-- Prove2me | Theorems.Thm_PI_QnRT_w_row_other
-- name    : PI.QnRT.w_row_other
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:19:16.907802+00:00
-- url     : https://prove2.me/theorems/fa462d72-f456-5f9e-8241-878f610d643a
-- title:
--   Qn RT: w row other
-- statement:
--   The Qn RT construction uses the w row other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L105-L111

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

theorem PI.QnRT.w_row_other (l : Fin r) (a : ℂ) (s q : Fin (2 * r + k + 1)) (hs1 : s ≠ eI k r l)
    (hs2 : s ≠ esI k r l) : w1 k r l a s q = if s = q then 1 else 0 := by sorry
