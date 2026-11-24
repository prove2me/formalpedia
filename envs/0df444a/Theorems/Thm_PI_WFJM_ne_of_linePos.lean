-- Prove2me | Theorems.Thm_PI_WFJM_ne_of_linePos
-- name    : PI.WFJM.ne_of_linePos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:18.176387+00:00
-- url     : https://prove2.me/theorems/82d151a9-66cd-41af-88bb-fb847cfc4dbb
-- title:
--   WFJM: ne of line Pos
-- statement:
--   The WFJM construction uses the ne of line Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L439-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L439-L441

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

theorem PI.WFJM.ne_of_linePos {p q r s : ℕ} {l l' : Ln p q r s} (h : linePos l ≠ linePos l') : l ≠ l' := by sorry
