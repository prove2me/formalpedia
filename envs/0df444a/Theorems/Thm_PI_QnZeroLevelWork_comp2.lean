-- Prove2me | Theorems.Thm_PI_QnZeroLevelWork_comp2
-- name    : PI.QnZeroLevelWork.comp2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:20:06.97567+00:00
-- url     : https://prove2.me/theorems/d82c4b45-8c08-4600-bbe6-f41d7db213c5
-- title:
--   Qn Zero Level Work: comp2
-- statement:
--   The Qn Zero Level Work construction uses the comp2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L91-L95

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

theorem PI.QnZeroLevelWork.comp2 (i : Fin (2 * r + k + 2)) (i'' : Fin (2 * r + k + 1)) (h : (i : ℕ) ≤ (i'' : ℕ)) :
    (posL (k + 1) r 0 ∘ skip2 i (i.succAbove i'') : Fin (2 * r + k + 2 - 2) → Fin (2 * r + (k + 1) + 1)) =
      drop2 i i'' := by sorry
