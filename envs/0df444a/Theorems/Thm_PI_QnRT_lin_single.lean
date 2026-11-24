-- Prove2me | Theorems.Thm_PI_QnRT_lin_single
-- name    : PI.QnRT.lin_single
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:58.232288+00:00
-- url     : https://prove2.me/theorems/0502b35b-2871-4678-a939-74af5510e4da
-- title:
--   Qn RT: lin single
-- statement:
--   The Qn RT construction uses the lin single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L304-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L304-L316

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

theorem PI.QnRT.lin_single {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r)
    (L : (Fin r → ℂ) →L[ℝ] E) (z : ℂ) :
    L (Pi.single l z) = (z.re : ℂ) • L (Pi.single l 1) + (z.im : ℂ) • L (Pi.single l Complex.I) := by sorry
