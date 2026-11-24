-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_hasDerivAt_D_of
-- name    : PI.ComplexConjugateDerivative.hasDerivAt_D_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:39:02.623032+00:00
-- url     : https://prove2.me/theorems/0cb7e0cf-b82a-49ed-900f-fa744aa9dc58
-- title:
--   Complex Conjugate Derivative: has Deriv At D of
-- statement:
--   The Complex Conjugate Derivative construction uses the has Deriv At D of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L287-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L287-L292

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

theorem PI.ComplexConjugateDerivative.hasDerivAt_D_of {b : Bool} {X g : B.Mat k r} {f : B.Mat k r → E} (hf : SS k r f)
    (hg : g ∈ B.GV k r) (hX : B.inLie k r X) :
    HasDerivAt (fun t : ℝ => f (cv b X g t)) (D b X f g) 0 := by sorry
