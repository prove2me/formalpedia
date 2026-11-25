-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_length_quot_add
-- name    : PI.UnitaryGroupMassFormula.BallQuotLen.length_quot_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:21.157924+00:00
-- url     : https://prove2.me/theorems/3c12f1fa-f286-4278-9fa7-f5fca187e994
-- title:
--   Ball Quot Len: length quot add
-- statement:
--   The Ball Quot Len construction uses the length quot add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L185-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L185-L221

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}

theorem PI.UnitaryGroupMassFormula.BallQuotLen.length_quot_add {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N P Q : Submodule R M} (h1 : N ≤ P) (h2 : P ≤ Q) :
    Module.length R (↥Q ⧸ N.comap Q.subtype) =
      Module.length R (↥P ⧸ N.comap P.subtype) + Module.length R (↥Q ⧸ P.comap Q.subtype) := by sorry
