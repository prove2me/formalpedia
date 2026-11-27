-- Prove2me | Theorems.Thm_PI_EF_lGrowth_of_right
-- name    : PI.EF.lGrowth_of_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:50.50211+00:00
-- url     : https://prove2.me/theorems/f40a611a-7595-4333-a7ff-fc070be1404e
-- title:
--   EF: l Growth of right
-- statement:
--   The EF construction uses the l Growth of right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFinal.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFinal.lean#L6-L9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthZeta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFinal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF

theorem PI.EF.lGrowth_of_right (hB : PI.LBoundRight) (hZ : PI.ZetaBoundRight) : LGrowth 7 300000 := by sorry
