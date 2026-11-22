-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_finite_pts
-- name    : PI.UnitaryGroupMassFormula.EfRankSum.finite_pts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:22:00.220316+00:00
-- url     : https://prove2.me/theorems/2919b388-37a2-4f11-a6e9-78f4df494312
-- title:
--   Ef Rank Sum: finite pts
-- statement:
--   The Ef Rank Sum construction uses the finite pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Points.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Points.lean#L33-L40

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Points
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

theorem PI.UnitaryGroupMassFormula.EfRankSum.finite_pts (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] : Finite (Pts O A) := by sorry
