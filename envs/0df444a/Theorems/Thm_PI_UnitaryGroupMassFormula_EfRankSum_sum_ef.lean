-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_sum_ef
-- name    : PI.UnitaryGroupMassFormula.EfRankSum.sum_ef
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:25.783925+00:00
-- url     : https://prove2.me/theorems/9fda9b5d-4008-4aeb-9212-ae65f59cbc39
-- title:
--   Ef Rank Sum: sum ef
-- statement:
--   The Ef Rank Sum construction uses the sum ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/EfRankSumMain.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/EfRankSumMain.lean#L8-L19

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

theorem PI.UnitaryGroupMassFormula.EfRankSum.sum_ef (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] [Module.Flat O ↥(As O A)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank O ↥(As O A) := by sorry
