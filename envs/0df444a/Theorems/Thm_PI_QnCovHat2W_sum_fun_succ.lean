-- Prove2me | Theorems.Thm_PI_QnCovHat2W_sum_fun_succ
-- name    : PI.QnCovHat2W.sum_fun_succ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:54:08.993147+00:00
-- url     : https://prove2.me/theorems/ada25ecd-db69-4127-a79b-35b5526fb012
-- title:
--   Qn Cov Hat2 W: sum fun succ
-- statement:
--   The Qn Cov Hat2 W construction uses the sum fun succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L13-L17

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnCovHat2W.sum_fun_succ {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (f : (Fin (r + 1) → α) → M) :
    ∑ x, f x = ∑ x0 : α, ∑ y : Fin r → α, f (Fin.cons x0 y) := by sorry
