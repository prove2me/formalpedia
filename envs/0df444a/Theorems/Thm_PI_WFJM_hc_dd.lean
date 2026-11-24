-- Prove2me | Theorems.Thm_PI_WFJM_hc_dd
-- name    : PI.WFJM.hc_dd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:05.210157+00:00
-- url     : https://prove2.me/theorems/b49f96a4-ad4d-4e2f-9264-0ee8e12bb495
-- title:
--   WFJM: hc dd
-- statement:
--   The WFJM construction uses the hc dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L427-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L427-L431

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

theorem PI.WFJM.hc_dd {p q r s : ℕ} (l l' : Ln p q r s) (e : ℕ) (P : Pol p q r s) :
    MvPolynomial.homogeneousComponent e (dd l l' P) = dd l l' (MvPolynomial.homogeneousComponent (e + 2) P) := by sorry
