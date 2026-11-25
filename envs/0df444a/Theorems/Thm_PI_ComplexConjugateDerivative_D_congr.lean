-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_D_congr
-- name    : PI.ComplexConjugateDerivative.D_congr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:26:52.165901+00:00
-- url     : https://prove2.me/theorems/30b7e892-b732-42e4-948b-f698bcface05
-- title:
--   Complex Conjugate Derivative: D congr
-- statement:
--   The Complex Conjugate Derivative construction uses the D congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L294-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L294-L300

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

theorem PI.ComplexConjugateDerivative.D_congr {b : Bool} {X g : B.Mat k r} {f₁ f₂ : B.Mat k r → E}
    (h : ∀ y ∈ B.GV k r, f₁ y = f₂ y) (hg : g ∈ B.GV k r) (hX : B.inLie k r X) :
    D b X f₁ g = D b X f₂ g := by sorry
