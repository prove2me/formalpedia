-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_D_add
-- name    : PI.ComplexConjugateDerivative.D_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:26:46.952994+00:00
-- url     : https://prove2.me/theorems/dacd86e0-863e-47a6-9fac-c34f81fb9a0b
-- title:
--   Complex Conjugate Derivative: D add
-- statement:
--   The Complex Conjugate Derivative construction uses the D add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L302-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L302-L306

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

theorem PI.ComplexConjugateDerivative.D_add {b : Bool} {X g : B.Mat k r} {f₁ f₂ : B.Mat k r → E} (h₁ : SS k r f₁) (h₂ : SS k r f₂)
    (hg : g ∈ B.GV k r) (hX : B.inLie k r X) :
    D b X (f₁ + f₂) g = D b X f₁ g + D b X f₂ g := by sorry
