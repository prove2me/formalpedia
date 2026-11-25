-- Prove2me | Theorems.Thm_PI_WFJM_fockAct1_expand
-- name    : PI.WFJM.fockAct1_expand
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:11.804222+00:00
-- url     : https://prove2.me/theorems/38374c6a-50e6-4fca-bee6-58ee7e841bb1
-- title:
--   WFJM: fock Act1 expand
-- statement:
--   The WFJM construction uses the fock Act1 expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L524-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L524-L527

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

theorem PI.WFJM.fockAct1_expand (X : Mat p q) :
    fockAct1 p q r s X = ∑ a, ∑ b, X a b • fockAct1 p q r s (Eab a b) := by sorry
