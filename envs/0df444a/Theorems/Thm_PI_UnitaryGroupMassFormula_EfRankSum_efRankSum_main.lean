-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_efRankSum_main
-- name    : PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:24.697364+00:00
-- url     : https://prove2.me/theorems/58d85d34-3344-4c48-bca5-5b1da6c6ce3d
-- title:
--   Ef Rank Sum: ef Rank Sum main
-- statement:
--   The Ef Rank Sum construction uses the ef Rank Sum main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/EfRankSumMain.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/EfRankSumMain.lean#L21-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Lattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Points
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_EfRankSumMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.EfRankSum
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing

theorem PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main : PI.EfRankSum := by sorry
