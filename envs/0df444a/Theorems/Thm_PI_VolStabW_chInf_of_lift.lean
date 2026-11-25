-- Prove2me | Theorems.Thm_PI_VolStabW_chInf_of_lift
-- name    : PI.VolStabW.chInf_of_lift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:42:44.275265+00:00
-- url     : https://prove2.me/theorems/b42be2a8-3c8e-4213-bbd6-7b75d7b2db31
-- title:
--   Vol Stab W: ch Inf of lift
-- statement:
--   The Vol Stab W construction uses the ch Inf of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensSAInt.lean#L87-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensSAInt.lean#L87-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open PI PI.VolStabW

theorem PI.VolStabW.chInf_of_lift (hL : ChLift) : ChInf := by sorry
