-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_bsum_nonneg
-- name    : PI.ComplexConjugateDerivative.bsum_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:28.565837+00:00
-- url     : https://prove2.me/theorems/495c68bb-d77a-4d6f-bc0d-5a0d92c161cf
-- title:
--   Complex Conjugate Derivative: bsum nonneg
-- statement:
--   The Complex Conjugate Derivative construction uses the bsum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L104-L109

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

theorem PI.ComplexConjugateDerivative.bsum_nonneg {N : ℕ} (e : Fin N → B.Mat k r) :
    ∀ (ks : List Bool) (Ψ : List (B.Mat k r) → ℝ), (∀ β, 0 ≤ Ψ β) → 0 ≤ bsum e ks Ψ
  := by sorry
