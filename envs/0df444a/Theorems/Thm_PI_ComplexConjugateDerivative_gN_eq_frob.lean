-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_gN_eq_frob
-- name    : PI.ComplexConjugateDerivative.gN_eq_frob
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:26:14.013052+00:00
-- url     : https://prove2.me/theorems/af2e2e1b-a348-58b4-b93a-a76c2b654459
-- title:
--   Complex Conjugate Derivative: g N eq frob
-- statement:
--   The Complex Conjugate Derivative construction uses the g N eq frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L112-L118

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
open scoped Matrix.Norms.Frobenius

theorem PI.ComplexConjugateDerivative.gN_eq_frob (g : B.Mat k r) : B.gN g = ‖g‖ := by sorry
