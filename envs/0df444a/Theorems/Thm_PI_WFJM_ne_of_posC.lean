-- Prove2me | Theorems.Thm_PI_WFJM_ne_of_posC
-- name    : PI.WFJM.ne_of_posC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:32.52414+00:00
-- url     : https://prove2.me/theorems/fd0e6cb8-635b-41f2-ac49-6159140c97f2
-- title:
--   WFJM: ne of pos C
-- statement:
--   The WFJM construction uses the ne of pos C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L655-L660
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L655-L660

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

theorem PI.WFJM.ne_of_posC {n k : ℕ} {a b : Ix n k} (h : posC a b) : a ≠ b := by sorry
