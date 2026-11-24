-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_D_eq_fderiv
-- name    : PI.ComplexConjugateDerivative.D_eq_fderiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:07.020429+00:00
-- url     : https://prove2.me/theorems/fe5eab9b-437b-4f11-a1d5-778987d8aa19
-- title:
--   Complex Conjugate Derivative: D eq fderiv
-- statement:
--   The Complex Conjugate Derivative construction uses the D eq fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L262-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L262-L267

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

theorem PI.ComplexConjugateDerivative.D_eq_fderiv {b : Bool} {X g : B.Mat k r} {f f' : B.Mat k r → E} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hgU : g ∈ U) (hgG : g ∈ B.GV k r) (hfe : ∀ h ∈ U, h ∈ B.GV k r → f h = f' h)
    (hd : DifferentiableAt ℝ f' g) (hX : B.inLie k r X) :
    D b X f g = fderiv ℝ f' g (vel b X g) := by sorry
