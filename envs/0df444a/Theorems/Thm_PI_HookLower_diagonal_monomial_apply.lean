-- Prove2me | Theorems.Thm_PI_HookLower_diagonal_monomial_apply
-- name    : PI.HookLower.diagonal_monomial_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:06:46.770287+00:00
-- url     : https://prove2.me/theorems/8b2161fc-12ad-416a-b5b1-55c90a9e7a38
-- title:
--   Hook Lower: diagonal monomial apply
-- statement:
--   The Hook Lower construction uses the diagonal monomial apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L107-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L107-L117

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookLower

theorem PI.HookLower.diagonal_monomial_apply {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) (a : Fin N) : M0 ν (a, a) = ν a := by sorry
