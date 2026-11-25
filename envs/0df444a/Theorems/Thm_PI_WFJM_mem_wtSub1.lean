-- Prove2me | Theorems.Thm_PI_WFJM_mem_wtSub1
-- name    : PI.WFJM.mem_wtSub1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:43:57.609797+00:00
-- url     : https://prove2.me/theorems/2d917ad5-37b9-4fc2-b757-1405d03f6f9e
-- title:
--   WFJM: mem wt Sub1
-- statement:
--   The WFJM construction uses the mem wt Sub1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L621-L636
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L621-L636

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
variable {p q r s : ℕ}
open MvPolynomial

theorem PI.WFJM.mem_wtSub1 (μ : Ix p q → ℚ) (P : Pol p q r s) :
    P ∈ wtSub (fockAct1 p q r s) μ ↔ ∀ m ∈ P.support, ∀ a, (wt1 m a : ℚ) + sh1 p q r s a = μ a := by sorry
