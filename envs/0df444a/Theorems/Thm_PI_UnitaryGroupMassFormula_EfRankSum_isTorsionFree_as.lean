-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_isTorsionFree_as
-- name    : PI.UnitaryGroupMassFormula.EfRankSum.isTorsionFree_as
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:21.620818+00:00
-- url     : https://prove2.me/theorems/e3381ac7-ad85-4c17-b0ba-f746d045c7ad
-- title:
--   Ef Rank Sum: is Torsion Free as
-- statement:
--   The Ef Rank Sum construction uses the is Torsion Free as property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Lattice.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Lattice.lean#L23-L32

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

theorem PI.UnitaryGroupMassFormula.EfRankSum.isTorsionFree_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O ↥(As O A) := by sorry
