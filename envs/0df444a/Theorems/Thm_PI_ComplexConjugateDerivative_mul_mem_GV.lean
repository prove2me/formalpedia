-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_mul_mem_GV
-- name    : PI.ComplexConjugateDerivative.mul_mem_GV
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:26:52.157279+00:00
-- url     : https://prove2.me/theorems/29a3cb22-e98f-49cd-b5b8-daab50812669
-- title:
--   Complex Conjugate Derivative: mul mem GV
-- statement:
--   The Complex Conjugate Derivative construction uses the mul mem GV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L68-L74

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

theorem PI.ComplexConjugateDerivative.mul_mem_GV {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) : a * b ∈ B.GV k r := by sorry
