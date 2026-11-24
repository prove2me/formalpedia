-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_D_eq
-- name    : PI.ComplexConjugateDerivative.D_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:55:32.694807+00:00
-- url     : https://prove2.me/theorems/cce26115-82b0-4bdc-b487-1e672f0e1d67
-- title:
--   Complex Conjugate Derivative: D eq
-- statement:
--   The Complex Conjugate Derivative construction uses the D eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L186-L188

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
variable {k r : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.ComplexConjugateDerivative.D_eq (b : Bool) (X : B.Mat k r) (f : B.Mat k r → E) (g : B.Mat k r) :
    D b X f g = deriv (fun t : ℝ => f (cv b X g t)) 0 := by sorry
