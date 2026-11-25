-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_eq_zero_of_ord_top
-- name    : PI.UnitaryGroupMassFormula.BallQuotLen.eq_zero_of_ord_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:43.050252+00:00
-- url     : https://prove2.me/theorems/b59ec2e0-0056-4df5-82d6-375a0259e995
-- title:
--   Ball Quot Len: eq zero of ord top
-- statement:
--   The Ball Quot Len construction uses the eq zero of ord top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L18-L32

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

theorem PI.UnitaryGroupMassFormula.BallQuotLen.eq_zero_of_ord_top [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {x : A}
    (hx : ∀ ζ : Pts O A, ord ϖ ζ x = ⊤) : x = 0 := by sorry
