-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_sgI_lt
-- name    : PI.ComplexConjugateDerivative.sgI_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:27:01.554314+00:00
-- url     : https://prove2.me/theorems/7c51993e-79fa-58ba-83d6-4e5aa468eb4e
-- title:
--   Complex Conjugate Derivative: sg I lt
-- statement:
--   The Complex Conjugate Derivative construction uses the sg I lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L22-L25

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

theorem PI.ComplexConjugateDerivative.sgI_lt (i : Fin (2 * r + k + 1)) : sgI k r i.val < 2 * r + k + 1 := by sorry
