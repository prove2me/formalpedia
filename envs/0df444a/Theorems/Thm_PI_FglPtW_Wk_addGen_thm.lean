-- Prove2me | Theorems.Thm_PI_FglPtW_Wk_addGen_thm
-- name    : PI.FglPtW.Wk.addGen_thm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:06.325709+00:00
-- url     : https://prove2.me/theorems/2aa58a49-bcc2-4933-8186-945d1543ff97
-- title:
--   Wk: add Gen thm
-- statement:
--   The Wk construction uses the add Gen thm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/AddGenThm.lean#L9-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/AddGenThm.lean#L9-L61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffPsubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_AddGenThm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPtW PI.FglPtW.Wk
open PI.AddIntG.Wk

theorem PI.FglPtW.Wk.addGen_thm : PI.FglPtW.AddGen := by sorry
