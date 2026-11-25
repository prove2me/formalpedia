-- Prove2me | Theorems.Thm_PI_WFJM_fockAct2_expand
-- name    : PI.WFJM.fockAct2_expand
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:08.660911+00:00
-- url     : https://prove2.me/theorems/5499c830-6978-5560-95ba-b355d7babdb1
-- title:
--   WFJM: fock Act2 expand
-- statement:
--   The WFJM construction uses the fock Act2 expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L529-L534
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L529-L534

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

theorem PI.WFJM.fockAct2_expand (Y : Mat r s) :
    fockAct2 p q r s Y = ∑ c, ∑ d, Y c d • fockAct2 p q r s (Eab c d) := by sorry
