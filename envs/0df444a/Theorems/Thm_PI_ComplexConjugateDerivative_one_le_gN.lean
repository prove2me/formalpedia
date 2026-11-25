-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_one_le_gN
-- name    : PI.ComplexConjugateDerivative.one_le_gN
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:26:55.320806+00:00
-- url     : https://prove2.me/theorems/8f36ff86-97d2-4e31-842c-3bf5bc2ee71c
-- title:
--   Complex Conjugate Derivative: one le g N
-- statement:
--   The Complex Conjugate Derivative construction uses the one le g N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L120-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L120-L132

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

theorem PI.ComplexConjugateDerivative.one_le_gN {g : B.Mat k r} (hg : g ∈ B.GV k r) : 1 ≤ B.gN g := by sorry
