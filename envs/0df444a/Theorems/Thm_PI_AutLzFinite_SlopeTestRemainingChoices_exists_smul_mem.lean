-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_exists_smul_mem
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.exists_smul_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:38.862065+00:00
-- url     : https://prove2.me/theorems/2768aaa2-1220-4545-8306-ddd946918ce0
-- title:
--   Slope Test Remaining Choices: exists smul mem
-- statement:
--   The Slope Test Remaining Choices construction uses the exists smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/FiniteOfIntegralBound.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/FiniteOfIntegralBound.lean#L14-L16

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

theorem PI.AutLzFinite.SlopeTestRemainingChoices.exists_smul_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by sorry
