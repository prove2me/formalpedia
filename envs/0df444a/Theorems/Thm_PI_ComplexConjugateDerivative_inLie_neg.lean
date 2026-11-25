-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_inLie_neg
-- name    : PI.ComplexConjugateDerivative.inLie_neg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:26:23.810851+00:00
-- url     : https://prove2.me/theorems/d7c6051b-db15-4417-86cc-cadad345681d
-- title:
--   Complex Conjugate Derivative: in Lie neg
-- statement:
--   The Complex Conjugate Derivative construction uses the in Lie neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L76-L78

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

theorem PI.ComplexConjugateDerivative.inLie_neg {X : B.Mat k r} (hX : B.inLie k r X) : B.inLie k r (-X) := by sorry
