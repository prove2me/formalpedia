-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_subgroup_locally_compact_holds
-- name    : PI.VolSemiDirect.W.subgroup_locally_compact_holds
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:29.154129+00:00
-- url     : https://prove2.me/theorems/184db36e-aa08-46a0-a64c-8b7384ae1a6b
-- title:
--   W: subgroup locally compact holds
-- statement:
--   The W construction uses the subgroup locally compact holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/SubgroupLocallyCompactHolds.lean#L8-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/SubgroupLocallyCompactHolds.lean#L8-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SubgroupLocallyCompactHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W

theorem PI.VolSemiDirect.W.subgroup_locally_compact_holds : SubLCSC := by sorry
