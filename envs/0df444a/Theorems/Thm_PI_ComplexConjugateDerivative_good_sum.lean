-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_good_sum
-- name    : PI.ComplexConjugateDerivative.good_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:26:30.278594+00:00
-- url     : https://prove2.me/theorems/a2f76ace-39e7-4761-94e1-ce1dfccbc6fa
-- title:
--   Complex Conjugate Derivative: good sum
-- statement:
--   The Complex Conjugate Derivative construction uses the good sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L34-L49

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

theorem PI.ComplexConjugateDerivative.good_sum {Φ : (B.Mat k r → E) → (B.Mat k r → E)} (hΦ : Good Φ) {N : ℕ} (c : Fin N → ℝ)
    (h : Fin N → B.Mat k r → E) (hh : ∀ i, SS k r (h i)) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Φ (∑ i, c i • h i) g = ∑ i, c i • Φ (h i) g := by sorry
