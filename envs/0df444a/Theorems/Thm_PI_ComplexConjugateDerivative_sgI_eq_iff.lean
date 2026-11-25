-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_sgI_eq_iff
-- name    : PI.ComplexConjugateDerivative.sgI_eq_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:26:39.931527+00:00
-- url     : https://prove2.me/theorems/f2b80942-aee0-5f99-b1e6-3bd3c4ae8a19
-- title:
--   Complex Conjugate Derivative: sg I eq iff
-- statement:
--   The Complex Conjugate Derivative construction uses the sg I eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L32-L35

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

theorem PI.ComplexConjugateDerivative.sgI_eq_iff (i : Fin (2 * r + k + 1)) : sgI k r i.val = r + k ↔ i.val = r + k := by sorry
