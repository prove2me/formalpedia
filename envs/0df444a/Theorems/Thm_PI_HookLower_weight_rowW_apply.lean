-- Prove2me | Theorems.Thm_PI_HookLower_weight_rowW_apply
-- name    : PI.HookLower.weight_rowW_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:06:41.704435+00:00
-- url     : https://prove2.me/theorems/183d31e3-2b49-4e23-8e27-885f383651cb
-- title:
--   Hook Lower: weight row W apply
-- statement:
--   The Hook Lower construction uses the weight row W apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L95-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L95-L105

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

theorem PI.HookLower.weight_rowW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    (Finsupp.weight (rowW N N) m) a = ∑ b : Fin N, m (a, b) := by sorry
