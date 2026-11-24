-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_hasDerivAt_D
-- name    : PI.ComplexConjugateDerivative.hasDerivAt_D
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:39:12.650385+00:00
-- url     : https://prove2.me/theorems/963d1b05-aa6f-466f-ae66-cc646000012d
-- title:
--   Complex Conjugate Derivative: has Deriv At D
-- statement:
--   The Complex Conjugate Derivative construction uses the has Deriv At D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L246-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L246-L260

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

theorem PI.ComplexConjugateDerivative.hasDerivAt_D {b : Bool} {X g : B.Mat k r} {f f' : B.Mat k r → E} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hgU : g ∈ U) (hgG : g ∈ B.GV k r) (hfe : ∀ h ∈ U, h ∈ B.GV k r → f h = f' h)
    (hd : DifferentiableAt ℝ f' g) (hX : B.inLie k r X) :
    HasDerivAt (fun t : ℝ => f (cv b X g t)) (fderiv ℝ f' g (vel b X g)) 0 := by sorry
