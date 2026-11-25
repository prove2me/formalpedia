-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_cst_spec
-- name    : PI.ComplexConjugateDerivative.cst_spec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:27:11.573385+00:00
-- url     : https://prove2.me/theorems/d5ae7df1-9e3c-4648-a12c-43143b41ee41
-- title:
--   Complex Conjugate Derivative: cst spec
-- statement:
--   The Complex Conjugate Derivative construction uses the cst spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L231-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L231-L236

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

theorem PI.ComplexConjugateDerivative.cst_spec {A : ℝ} {F : B.Mat k r → E} (hF : C2.CCsc k r A F) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.unitLie k r X) (hv : ∀ X ∈ v, B.unitLie k r X) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    B.gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) * ‖B.dLR u v F g‖ ≤ cst hF u v := by sorry
