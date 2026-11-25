-- Prove2me | Theorems.Thm_PI_WFJM_mulXX_homog
-- name    : PI.WFJM.mulXX_homog
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:15.261865+00:00
-- url     : https://prove2.me/theorems/fed38626-2310-4915-8882-42a8ff4addce
-- title:
--   WFJM: mul XX homog
-- statement:
--   The WFJM construction uses the mul XX homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L418-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L418-L423

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

theorem PI.WFJM.mulXX_homog (l l' : σ) (d : ℕ) (Q : MvPolynomial σ ℂ) (hQ : Q ∈ homog σ d) :
    ((LinearMap.mulLeft ℂ (X l) * LinearMap.mulLeft ℂ (X l') : Module.End ℂ (MvPolynomial σ ℂ)) Q) ∈
      homog σ (d + 2) := by sorry
