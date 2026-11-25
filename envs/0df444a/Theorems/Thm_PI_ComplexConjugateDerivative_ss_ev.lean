-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_ss_ev
-- name    : PI.ComplexConjugateDerivative.ss_ev
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:27:12.119822+00:00
-- url     : https://prove2.me/theorems/61d310ca-3da2-59ff-9f65-00dc7dbb9be0
-- title:
--   Complex Conjugate Derivative: ss ev
-- statement:
--   The Complex Conjugate Derivative construction uses the ss ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L55-L61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder
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
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.ComplexConjugateDerivative.ss_ev : ∀ (ks : List Bool) (xs : List (B.Mat k r)) {f : B.Mat k r → E},
    (∀ X ∈ xs, B.inLie k r X) → SS k r f → SS k r (ev ks xs f)
  := by sorry
