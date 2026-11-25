-- Prove2me | Theorems.Thm_PI_QnZeroLevelWork_comp1
-- name    : PI.QnZeroLevelWork.comp1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:20:42.0698+00:00
-- url     : https://prove2.me/theorems/d9861114-b2ca-422b-98d2-b9ff3868afce
-- title:
--   Qn Zero Level Work: comp1
-- statement:
--   The Qn Zero Level Work construction uses the comp1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L86-L89

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnZeroLevelWork
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}

theorem PI.QnZeroLevelWork.comp1 (i : Fin (2 * r + k + 2)) :
    (posL (k + 1) r 0 ∘ skip1 i : Fin (2 * r + k + 2 - 1) → Fin (2 * r + (k + 1) + 1)) = i.succAbove := by sorry
