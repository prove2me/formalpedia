-- Prove2me | Theorems.Thm_PI_FJMX_getD_succ_le
-- name    : PI.FJMX.getD_succ_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:24.212789+00:00
-- url     : https://prove2.me/theorems/ec86dadc-2c65-4e3c-81c3-95e07a1b7fd9
-- title:
--   FJMX: get D succ le
-- statement:
--   The FJMX construction uses the get D succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistWt.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistWt.lean#L28-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX

theorem PI.FJMX.getD_succ_le (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) (t : ℕ) :
    α.getD (t + 1) 0 ≤ α.getD t 0 := by sorry
