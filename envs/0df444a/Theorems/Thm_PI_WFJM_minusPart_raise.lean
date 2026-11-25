-- Prove2me | Theorems.Thm_PI_WFJM_minusPart_raise
-- name    : PI.WFJM.minusPart_raise
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:03.439921+00:00
-- url     : https://prove2.me/theorems/0c7a0aa6-eeef-4290-80d9-d303ce974346
-- title:
--   WFJM: minus Part raise
-- statement:
--   The WFJM construction uses the minus Part raise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L385-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L385-L391

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
open MvPolynomial
variable {σ : Type*}

theorem PI.WFJM.minusPart_raise (A : Module.End ℂ (MvPolynomial σ ℂ))
    (hA : ∀ (d : ℕ) (Q : MvPolynomial σ ℂ), Q ∈ homog σ d → A Q ∈ homog σ (d + 2))
    (P : MvPolynomial σ ℂ) : minusPart A P = 0 := by sorry
