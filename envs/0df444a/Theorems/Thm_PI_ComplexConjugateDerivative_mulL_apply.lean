-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_mulL_apply
-- name    : PI.ComplexConjugateDerivative.mulL_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:26:37.990356+00:00
-- url     : https://prove2.me/theorems/6d55b547-af45-404f-90f5-f760ba7bcf6f
-- title:
--   Complex Conjugate Derivative: mul L apply
-- statement:
--   The Complex Conjugate Derivative construction uses the mul L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L169-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L169-L169

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

theorem PI.ComplexConjugateDerivative.mulL_apply (a x : Matrix (Fin n) (Fin n) ℂ) : mulL a x = a * x := by sorry
