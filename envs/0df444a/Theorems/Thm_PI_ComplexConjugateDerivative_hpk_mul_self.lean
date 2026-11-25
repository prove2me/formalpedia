-- Prove2me | Theorems.Thm_PI_ComplexConjugateDerivative_hpk_mul_self
-- name    : PI.ComplexConjugateDerivative.hpk_mul_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:39:11.675803+00:00
-- url     : https://prove2.me/theorems/29196079-b8f1-4031-8c6c-ffc25c7a8a77
-- title:
--   Complex Conjugate Derivative: hpk mul self
-- statement:
--   The Complex Conjugate Derivative construction uses the hpk mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L37-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/HasDerivAtDOf.lean#L37-L54

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

theorem PI.ComplexConjugateDerivative.hpk_mul_self : Hpk k r * Hpk k r = 1 := by sorry
