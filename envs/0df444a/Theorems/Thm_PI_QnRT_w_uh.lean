-- Prove2me | Theorems.Thm_PI_QnRT_w_uh
-- name    : PI.QnRT.w_uh
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:20:04.903034+00:00
-- url     : https://prove2.me/theorems/4cb28ad9-5c4b-5fb6-847d-55c38ad0efe7
-- title:
--   Qn RT: w uh
-- statement:
--   The Qn RT construction uses the w uh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L185-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/WColOther.lean#L185-L214

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

theorem PI.QnRT.w_uh (l : Fin r) (a : ℂ) (ha : a ≠ 0) : w1 k r l a ∈ UH (Hpk k r) := by sorry
