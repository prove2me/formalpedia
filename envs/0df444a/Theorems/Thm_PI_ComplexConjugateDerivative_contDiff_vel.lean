-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_contDiff_vel
-- name    : PI.ComplexConjugateDerivative.contDiff_vel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:27:06.645171+00:00
-- url     : https://prove2.me/theorems/b17a9c93-2af4-4ab1-92d9-244858d2d9e3
-- title:
--   Complex Conjugate Derivative: cont Diff vel
-- statement:
--   The Complex Conjugate Derivative construction uses the cont Diff vel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L228-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L228-L236

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

theorem PI.ComplexConjugateDerivative.contDiff_vel (b : Bool) (X : B.Mat k r) {m : WithTop ℕ∞} :
    ContDiff ℝ m (fun h : B.Mat k r => vel b X h) := by sorry
