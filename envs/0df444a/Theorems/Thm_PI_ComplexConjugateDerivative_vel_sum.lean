-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_vel_sum
-- name    : PI.ComplexConjugateDerivative.vel_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:27:17.700519+00:00
-- url     : https://prove2.me/theorems/a284570d-a3e4-5a32-8941-3d752c1c2fc6
-- title:
--   Complex Conjugate Derivative: vel sum
-- statement:
--   The Complex Conjugate Derivative construction uses the vel sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L238-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L238-L244

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

theorem PI.ComplexConjugateDerivative.vel_sum (b : Bool) {N : ℕ} (c : Fin N → ℝ) (e : Fin N → B.Mat k r) (g : B.Mat k r) :
    vel b (∑ i, c i • e i) g = ∑ i, c i • vel b (e i) g := by sorry
