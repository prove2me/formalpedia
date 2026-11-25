-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_finrank_as
-- name    : PI.UnitaryGroupMassFormula.EfRankSum.finrank_as
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:23.221589+00:00
-- url     : https://prove2.me/theorems/8ac362a2-1243-4da5-a1c8-de7fedd94474
-- title:
--   Ef Rank Sum: finrank as
-- statement:
--   The Ef Rank Sum construction uses the finrank as property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Lattice.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Lattice.lean#L67-L75

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.EfRankSum
open Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem PI.UnitaryGroupMassFormula.EfRankSum.finrank_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    [Module.Finite O ↥(As O A)] : Module.finrank O ↥(As O A) = Module.finrank K A := by sorry
