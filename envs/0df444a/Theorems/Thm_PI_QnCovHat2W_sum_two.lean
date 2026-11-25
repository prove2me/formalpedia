-- Prove2me | Theorems.Thm_PI_QnCovHat2W_sum_two
-- name    : PI.QnCovHat2W.sum_two
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:26.557702+00:00
-- url     : https://prove2.me/theorems/b765d437-39ad-5ea3-b83a-bca4d1f2439f
-- title:
--   Qn Cov Hat2 W: sum two
-- statement:
--   The Qn Cov Hat2 W construction uses the sum two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L116-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L116-L138

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

theorem PI.QnCovHat2W.sum_two {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (m + 2) → α) (F : (Fin m → α) → M)
    (hF : ∀ (x : Fin m → α) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : α → ℂ) :
    ∑ c : Fin (m + 2) → α, sgnL c e • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β (e j) * β' (e (j.succAbove j'))) * (m.factorial : ℂ)) •
          F (fun k => e (j.succAbove (j'.succAbove k))) := by sorry
