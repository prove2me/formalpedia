-- Prove2me | Theorems.Thm_PI_QnRT_w_diff
-- name    : PI.QnRT.w_diff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:20:40.149486+00:00
-- url     : https://prove2.me/theorems/8e1de714-196a-413a-aa90-6dbedc729fac
-- title:
--   Qn RT: w diff
-- statement:
--   The Qn RT construction uses the w diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L214-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L214-L231

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

theorem PI.QnRT.w_diff (l : Fin r) (g₁ : Mx k r) (c : Fin r → ℂ) (hc : c l ≠ 0) :
    DifferentiableAt ℝ (fun c' : Fin r → ℂ => w1 k r l (c' l) * g₁) c := by sorry
