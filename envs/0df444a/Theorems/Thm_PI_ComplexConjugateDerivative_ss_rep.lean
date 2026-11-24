-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_ss_rep
-- name    : PI.ComplexConjugateDerivative.ss_rep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:39:18.604204+00:00
-- url     : https://prove2.me/theorems/50233816-3af5-4268-8fe9-a481f2da297f
-- title:
--   Complex Conjugate Derivative: ss rep
-- statement:
--   The Complex Conjugate Derivative construction uses the ss rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L271-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L271-L275

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

theorem PI.ComplexConjugateDerivative.ss_rep {f : B.Mat k r → E} (hf : SS k r f) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    ∃ (U : Set (B.Mat k r)) (f' : B.Mat k r → E), IsOpen U ∧ g ∈ U ∧ DifferentiableAt ℝ f' g ∧
      ∀ h ∈ U, h ∈ B.GV k r → f h = f' h := by sorry
