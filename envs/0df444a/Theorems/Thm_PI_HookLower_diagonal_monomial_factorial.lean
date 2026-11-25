-- Prove2me | Theorems.Thm_PI_HookLower_diagonal_monomial_factorial
-- name    : PI.HookLower.diagonal_monomial_factorial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:22.569157+00:00
-- url     : https://prove2.me/theorems/10a112b4-2744-4677-b305-c14b3969951d
-- title:
--   Hook Lower: diagonal monomial factorial
-- statement:
--   The Hook Lower construction uses the diagonal monomial factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L119-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L119-L131

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

theorem PI.HookLower.diagonal_monomial_factorial {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) :
    (∏ k ∈ (M0 ν).support, ((M0 ν) k).factorial) = ∏ l, (ν l).factorial := by sorry
