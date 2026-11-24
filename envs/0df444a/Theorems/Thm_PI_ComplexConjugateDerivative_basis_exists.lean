-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_basis_exists
-- name    : PI.ComplexConjugateDerivative.basis_exists
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:17.201173+00:00
-- url     : https://prove2.me/theorems/8d1211fc-bb18-4afb-a38e-7cb3395935cc
-- title:
--   Complex Conjugate Derivative: basis exists
-- statement:
--   The Complex Conjugate Derivative construction uses the basis exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L179-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L179-L224

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

theorem PI.ComplexConjugateDerivative.basis_exists (k r : ℕ) : ∃ (N : ℕ) (e : Fin N → B.Mat k r) (c : Fin N → B.Mat k r → ℝ) (K : ℝ),
    0 ≤ K ∧ (∀ i, B.unitLie k r (e i)) ∧ (∀ X, B.inLie k r X → X = ∑ i, c i X • e i) ∧
    (∀ X, B.unitLie k r X → ∀ i, |c i X| ≤ K) := by sorry
