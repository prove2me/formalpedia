-- Prove2me | Theorems.Thm_PI_WFJM_omE_ne
-- name    : PI.WFJM.omE_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:25.663217+00:00
-- url     : https://prove2.me/theorems/ead48d93-2d87-4bc0-90c7-584eb97c94c5
-- title:
--   WFJM: om E ne
-- statement:
--   The WFJM construction uses the om E ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L129-L130

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

theorem PI.WFJM.omE_ne {p q r s : ℕ} {l l' : Ln p q r s} (h : l ≠ l') : omE l l' = raiB l * lowB l' := by sorry
