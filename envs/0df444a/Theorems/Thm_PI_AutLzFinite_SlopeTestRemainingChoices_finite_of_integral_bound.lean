-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_finite_of_integral_bound
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.finite_of_integral_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:22.505924+00:00
-- url     : https://prove2.me/theorems/c07665cb-ad57-4f04-ad6d-99bf05f2a224
-- title:
--   Slope Test Remaining Choices: finite of integral bound
-- statement:
--   The Slope Test Remaining Choices construction uses the finite of integral bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/FiniteOfIntegralBound.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/FiniteOfIntegralBound.lean#L18-L32

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight
import Definitions.Def_Lemmata_GeneralBFactThirdExtra_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_FiniteOfIntegralBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions NumberField
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem PI.AutLzFinite.SlopeTestRemainingChoices.finite_of_integral_bound (t : E) (ht : t ≠ 0) (C : ℝ) :
    {a : E | IsIntegral ℤ (t * a) ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ≤ C}.Finite := by sorry
