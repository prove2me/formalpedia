-- Prove2me | Theorems.Thm_PI_QnZeroLevelWork_pair_sum
-- name    : PI.QnZeroLevelWork.pair_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:20:09.645293+00:00
-- url     : https://prove2.me/theorems/8100cca9-ebec-5234-ab15-62db8904c521
-- title:
--   Qn Zero Level Work: pair sum
-- statement:
--   The Qn Zero Level Work construction uses the pair sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L43-L50

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

theorem PI.QnZeroLevelWork.pair_sum {M : Type*} [AddCommMonoid M] {n : ℕ} (i : Fin (n + 2)) (G : Fin (n + 2) → M) :
    (∑ i' : Fin (n + 2), if i < i' then G i' else 0) =
      ∑ i'' : Fin (n + 1), if (i : ℕ) ≤ (i'' : ℕ) then G (i.succAbove i'') else 0 := by sorry
