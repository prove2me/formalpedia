-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_tau_normSq
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.tau_normSq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:00.570494+00:00
-- url     : https://prove2.me/theorems/3ec8e91b-368f-4bc8-9319-605cad43d1e2
-- title:
--   Slope Test Remaining Choices: tau norm Sq
-- statement:
--   The Slope Test Remaining Choices construction uses the tau norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L52-L54

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight
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
open Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
variable {S}

theorem PI.AutLzFinite.SlopeTestRemainingChoices.tau_normSq {τ : E →+* ℂ} (hstar : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) (c : E) :
    τ (star c * c) = (Complex.normSq (τ c) : ℂ) := by sorry
