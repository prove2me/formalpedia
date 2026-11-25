-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_isUnit_of_ord_ne_top
-- name    : PI.UnitaryGroupMassFormula.BallQuotLen.isUnit_of_ord_ne_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:11.644165+00:00
-- url     : https://prove2.me/theorems/e9baebb7-8b20-44fd-a474-8183bd59b488
-- title:
--   Ball Quot Len: is Unit of ord ne top
-- statement:
--   The Ball Quot Len construction uses the is Unit of ord ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L34-L47

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

theorem PI.UnitaryGroupMassFormula.BallQuotLen.isUnit_of_ord_ne_top (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {x : A} (hx : ∀ ζ : Pts O A, ord ϖ ζ x ≠ ⊤) :
    IsUnit x := by sorry
