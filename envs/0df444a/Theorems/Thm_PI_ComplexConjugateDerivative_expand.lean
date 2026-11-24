-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_expand
-- name    : PI.ComplexConjugateDerivative.expand
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:39:27.804572+00:00
-- url     : https://prove2.me/theorems/27099eaf-7d06-42c9-96dc-fb87cc9f4ee5
-- title:
--   Complex Conjugate Derivative: expand
-- statement:
--   The Complex Conjugate Derivative construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L111-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L111-L159

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

theorem PI.ComplexConjugateDerivative.expand {N : ℕ} (e : Fin N → B.Mat k r) (c : Fin N → B.Mat k r → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ i, B.inLie k r (e i)) (hc : ∀ X, B.inLie k r X → X = ∑ i, c i X • e i) :
    ∀ (ks : List Bool) (xs : List (B.Mat k r)), xs.length = ks.length →
      (∀ X ∈ xs, B.inLie k r X ∧ ∀ i, |c i X| ≤ K) →
      ∀ (Φ : (B.Mat k r → E) → (B.Mat k r → E)), Good Φ → ∀ f, SS k r f → ∀ g ∈ B.GV k r,
        ‖Φ (ev ks xs f) g‖ ≤ K ^ xs.length * bsum e ks (fun β => ‖Φ (ev ks β f) g‖) := by sorry
