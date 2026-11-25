-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_hpk_ne_zero
-- name    : PI.ComplexConjugateDerivative.hpk_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:26:37.848419+00:00
-- url     : https://prove2.me/theorems/490a5a2c-b4ca-407e-bdbd-29f875ad55af
-- title:
--   Complex Conjugate Derivative: hpk ne zero
-- statement:
--   The Complex Conjugate Derivative construction uses the hpk ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L62-L66

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

theorem PI.ComplexConjugateDerivative.hpk_ne_zero : Hpk k r ≠ 0 := by sorry
