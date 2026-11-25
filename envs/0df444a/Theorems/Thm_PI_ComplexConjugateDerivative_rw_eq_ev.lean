-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_rw_eq_ev
-- name    : PI.ComplexConjugateDerivative.rw_eq_ev
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:27:10.03512+00:00
-- url     : https://prove2.me/theorems/ce8e3888-f5e5-493e-ad00-fc1b8fa9b717
-- title:
--   Complex Conjugate Derivative: rw eq ev
-- statement:
--   The Complex Conjugate Derivative construction uses the rw eq ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean#L63-L69

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

theorem PI.ComplexConjugateDerivative.rw_eq_ev (v : List (B.Mat k r)) (F : B.Mat k r → E) :
    B.Rw v F = ev (List.replicate v.length false) v F := by sorry
