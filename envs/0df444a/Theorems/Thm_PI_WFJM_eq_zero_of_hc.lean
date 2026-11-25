-- Prove2me | Theorems.Thm_PI_WFJM_eq_zero_of_hc
-- name    : PI.WFJM.eq_zero_of_hc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:16.849131+00:00
-- url     : https://prove2.me/theorems/9e3d6460-dc72-4710-b323-faaaa2ea8826
-- title:
--   WFJM: eq zero of hc
-- statement:
--   The WFJM construction uses the eq zero of hc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L332-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L332-L339

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

theorem PI.WFJM.eq_zero_of_hc (x : MvPolynomial σ ℂ) (h : ∀ e, homogeneousComponent e x = 0) :
    x = 0 := by sorry
