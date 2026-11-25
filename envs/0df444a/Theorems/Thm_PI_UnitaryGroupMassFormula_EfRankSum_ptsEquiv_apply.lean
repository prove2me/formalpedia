-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_ptsEquiv_apply
-- name    : PI.UnitaryGroupMassFormula.EfRankSum.ptsEquiv_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:09.269156+00:00
-- url     : https://prove2.me/theorems/c85a974f-36ea-4d3e-b8ca-98cd98813e0c
-- title:
--   Ef Rank Sum: pts Equiv apply
-- statement:
--   The Ef Rank Sum construction uses the pts Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Points.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Points.lean#L29-L31

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

theorem PI.UnitaryGroupMassFormula.EfRankSum.ptsEquiv_apply (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ((ptsEquiv O A ζ : (maximalIdeal O).primesOver ↥(As O A)) : Ideal ↥(As O A)) = ζ.asIdeal := by sorry
