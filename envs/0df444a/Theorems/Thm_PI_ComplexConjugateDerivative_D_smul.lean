-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_D_smul
-- name    : PI.ComplexConjugateDerivative.D_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:26:54.428732+00:00
-- url     : https://prove2.me/theorems/0e623d9d-4ffc-46d9-97d8-ea959a18b1ee
-- title:
--   Complex Conjugate Derivative: D smul
-- statement:
--   The Complex Conjugate Derivative construction uses the D smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L308-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L308-L312

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

theorem PI.ComplexConjugateDerivative.D_smul {b : Bool} {X g : B.Mat k r} (c : ℝ) {f : B.Mat k r → E} (hf : SS k r f)
    (hg : g ∈ B.GV k r) (hX : B.inLie k r X) :
    D b X (c • f) g = c • D b X f g := by sorry
