-- Prove2me | Theorems.Thm_PI_QnRT_w_fix
-- name    : PI.QnRT.w_fix
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:55.09792+00:00
-- url     : https://prove2.me/theorems/67d5d40e-b678-4e24-ba09-f5f2862f7feb
-- title:
--   Qn RT: w fix
-- statement:
--   The Qn RT construction uses the w fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L216-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L216-L220

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

theorem PI.QnRT.w_fix (l : Fin r) (a : ℂ) (x : Fin (2 * r + k + 1)) (h1 : x ≠ eI k r l) (h2 : x ≠ esI k r l) :
    w1 k r l a *ᵥ bvec x = bvec x := by sorry
