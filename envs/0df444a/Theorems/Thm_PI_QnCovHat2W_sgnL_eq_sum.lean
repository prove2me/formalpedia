-- Prove2me | Theorems.Thm_PI_QnCovHat2W_sgnL_eq_sum
-- name    : PI.QnCovHat2W.sgnL_eq_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:21.761038+00:00
-- url     : https://prove2.me/theorems/b6f930e4-43e8-5515-bdee-4a593c1347f1
-- title:
--   Qn Cov Hat2 W: sgn L eq sum
-- statement:
--   The Qn Cov Hat2 W construction uses the sgn L eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L19-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L19-L39

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

theorem PI.QnCovHat2W.sgnL_eq_sum {r : ℕ} {α : Type*} [DecidableEq α] (x e : Fin r → α) :
    sgnL x e = ∑ σ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (if x = e ∘ σ.symm then 1 else 0) := by sorry
