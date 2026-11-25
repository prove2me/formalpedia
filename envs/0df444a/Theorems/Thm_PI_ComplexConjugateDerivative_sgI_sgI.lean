-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_sgI_sgI
-- name    : PI.ComplexConjugateDerivative.sgI_sgI
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:26:46.466554+00:00
-- url     : https://prove2.me/theorems/91c8cfc3-2207-5274-8fd1-0e35f54e2f6f
-- title:
--   Complex Conjugate Derivative: sg I sg I
-- statement:
--   The Complex Conjugate Derivative construction uses the sg I sg I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L27-L30

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

theorem PI.ComplexConjugateDerivative.sgI_sgI (i : Fin (2 * r + k + 1)) : sgI k r (sgI k r i.val) = i.val := by sorry
