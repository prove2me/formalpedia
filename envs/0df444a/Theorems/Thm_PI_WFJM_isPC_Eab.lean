-- Prove2me | Theorems.Thm_PI_WFJM_isPC_Eab
-- name    : PI.WFJM.isPC_Eab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:54.789799+00:00
-- url     : https://prove2.me/theorems/c04f8452-9f5b-4542-8dd0-2b26642203e0
-- title:
--   WFJM: is PC Eab
-- statement:
--   The WFJM construction uses the is PC Eab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L546-L550
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L546-L550

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

theorem PI.WFJM.isPC_Eab {n m : ℕ} (a b : Ix n m) (h : ¬ sameBlock a b) : IsPC (Eab a b) := by sorry
