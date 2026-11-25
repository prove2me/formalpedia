-- Prove2me | Theorems.Thm_PI_QnCovHat2W_sum_sgnL_succ
-- name    : PI.QnCovHat2W.sum_sgnL_succ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:04:01.437666+00:00
-- url     : https://prove2.me/theorems/9f9dd487-f2cd-50e2-ab52-cbe0d84be2a1
-- title:
--   Qn Cov Hat2 W: sum sgn L succ
-- statement:
--   The Qn Cov Hat2 W construction uses the sum sgn L succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L66-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L66-L100

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

theorem PI.QnCovHat2W.sum_sgnL_succ {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (r + 1) → α) (H : (Fin (r + 1) → α) → M) :
    ∑ x, sgnL x e • H x = ∑ j : Fin (r + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      ∑ y : Fin r → α, sgnL y (e ∘ j.succAbove) • H (Fin.cons (e j) y) := by sorry
