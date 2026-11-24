-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_bsum_mono
-- name    : PI.ComplexConjugateDerivative.bsum_mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:39:25.743555+00:00
-- url     : https://prove2.me/theorems/c7042c7c-a682-4347-99de-260286b42c76
-- title:
--   Complex Conjugate Derivative: bsum mono
-- statement:
--   The Complex Conjugate Derivative construction uses the bsum mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L91-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L91-L102

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

theorem PI.ComplexConjugateDerivative.bsum_mono {N : ℕ} (e : Fin N → B.Mat k r) :
    ∀ (ks : List Bool) (Ψ₁ Ψ₂ : List (B.Mat k r) → ℝ),
      (∀ β : List (B.Mat k r), β.length = ks.length → (∀ x ∈ β, ∃ i, x = e i) → Ψ₁ β ≤ Ψ₂ β) →
      bsum e ks Ψ₁ ≤ bsum e ks Ψ₂
  := by sorry
