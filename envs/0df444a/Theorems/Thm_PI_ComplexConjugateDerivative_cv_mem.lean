-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_cv_mem
-- name    : PI.ComplexConjugateDerivative.cv_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:39:03.133845+00:00
-- url     : https://prove2.me/theorems/24da6d5f-974b-4a5c-ad1c-585227544cdd
-- title:
--   Complex Conjugate Derivative: cv mem
-- statement:
--   The Complex Conjugate Derivative construction uses the cv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L193-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L193-L202

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

theorem PI.ComplexConjugateDerivative.cv_mem {b : Bool} {X g : B.Mat k r} (hg : g ∈ B.GV k r) (hX : B.inLie k r X) (t : ℝ) :
    cv b X g t ∈ B.GV k r := by sorry
