-- Prove2me | Theorems.Thm_PI_QnZeroLevelWork_chat_eq
-- name    : PI.QnZeroLevelWork.chat_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:19:46.07909+00:00
-- url     : https://prove2.me/theorems/c313df2e-d790-5a78-bd83-47152022ecd1
-- title:
--   Qn Zero Level Work: chat eq
-- statement:
--   The Qn Zero Level Work construction uses the chat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L143-L146

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

theorem PI.QnZeroLevelWork.chat_eq (u : ℂ) (a β : Mx (k + 1) r → Fin (mdim (k + 1) r 0) → ℂ) (f : Mx (k + 1) r → E) :
    chatL (EH (k + 1) r) (posL (k + 1) r 0) u a β f =
      chatOp (m := 2 * r + k + 1) (EabH (Hpk (k + 1) r)) u a β f := by sorry
