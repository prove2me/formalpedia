-- Prove2me | Theorems.Thm_P2M_PI_QnZeroLevelWork_chat_eq__a258e55e8e4b
-- name    : P2M_PI_QnZeroLevelWork_chat_eq__a258e55e8e4b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:59:04.087338+00:00
-- url     : https://prove2.me/theorems/14655285-11e8-4e1d-9232-58b7a4ef9dd0
-- title:
--   P2 M PI Qn Zero Level Work chat eq  a258e55e8e4b: P2 M PI Qn Zero Level Work chat eq  a258e55e8e4b
-- statement:
--   The P2 M PI Qn Zero Level Work chat eq  a258e55e8e4b construction uses the P2 M PI Qn Zero Level Work chat eq  a258e55e8e4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L108-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean#L108-L118

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

theorem P2M_PI_QnZeroLevelWork_chat_eq__a258e55e8e4b (u : ℂ) (a β : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E) :
    chatL (EH (k + 1) r) (posL (k + 1) r 0) u a β f =
      chatOp (m := 2 * r + k + 1) (EabH (Hpk (k + 1) r)) u a β f := by sorry

alias «PI».«QnZeroLevelWork».«chat_eq'» := P2M_PI_QnZeroLevelWork_chat_eq__a258e55e8e4b
