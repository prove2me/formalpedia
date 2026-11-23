-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_isTorsionFree_alg
-- name    : PI.UnitaryGroupMassFormula.EfRankSum.isTorsionFree_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:10.425567+00:00
-- url     : https://prove2.me/theorems/b25b8698-fc6c-4f77-802b-14c391e1f3fe
-- title:
--   Ef Rank Sum: is Torsion Free alg
-- statement:
--   The Ef Rank Sum construction uses the is Torsion Free alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Lattice.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationRankSum/Lattice.lean#L7-L21

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

theorem PI.UnitaryGroupMassFormula.EfRankSum.isTorsionFree_alg (O : Type) [CommRing O] [IsDomain O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O A := by sorry
