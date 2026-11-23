-- Prove2me | Theorems.Thm_PI_FglPtW_Wk_mulGen_thm
-- name    : PI.FglPtW.Wk.mulGen_thm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:29.967707+00:00
-- url     : https://prove2.me/theorems/aa9052ee-3cc9-465e-8b66-ee6732810f34
-- title:
--   Wk: mul Gen thm
-- statement:
--   The Wk construction uses the mul Gen thm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/MulGenThm.lean#L9-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/MulGenThm.lean#L9-L53

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffPsubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_MulGenThm
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

theorem PI.FglPtW.Wk.mulGen_thm : PI.FglPtW.MulGen := by sorry
