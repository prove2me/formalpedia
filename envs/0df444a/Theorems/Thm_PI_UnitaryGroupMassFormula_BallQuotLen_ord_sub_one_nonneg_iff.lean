-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_ord_sub_one_nonneg_iff
-- name    : PI.UnitaryGroupMassFormula.BallQuotLen.ord_sub_one_nonneg_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:31.033289+00:00
-- url     : https://prove2.me/theorems/2e31dac8-1fd8-421e-8ae0-1e6393cd43bc
-- title:
--   Ball Quot Len: ord sub one nonneg iff
-- statement:
--   The Ball Quot Len construction uses the ord sub one nonneg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L172-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L172-L183

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

theorem PI.UnitaryGroupMassFormula.BallQuotLen.ord_sub_one_nonneg_iff (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (x : ↥(As O A)) :
    0 ≤ ord ϖ ζ (x : A) + ((-1 : ℤ) : WithTop ℤ) ↔ x ∈ ζ.asIdeal := by sorry
