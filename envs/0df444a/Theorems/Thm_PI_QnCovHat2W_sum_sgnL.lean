-- Prove2me | Theorems.Thm_PI_QnCovHat2W_sum_sgnL
-- name    : PI.QnCovHat2W.sum_sgnL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:00:13.793472+00:00
-- url     : https://prove2.me/theorems/fcc09bd8-3d1c-4163-91b3-9148bd5cdd92
-- title:
--   Qn Cov Hat2 W: sum sgn L
-- statement:
--   The Qn Cov Hat2 W construction uses the sum sgn L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L41-L47

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

theorem PI.QnCovHat2W.sum_sgnL {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin r → α) (g : (Fin r → α) → M) :
    ∑ x, sgnL x e • g x = ∑ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) • g (e ∘ π) := by sorry
