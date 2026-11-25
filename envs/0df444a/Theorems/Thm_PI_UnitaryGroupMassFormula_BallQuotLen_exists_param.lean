-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_exists_param
-- name    : PI.UnitaryGroupMassFormula.BallQuotLen.exists_param
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:29.342841+00:00
-- url     : https://prove2.me/theorems/64363765-97b2-57f7-bcfa-2393f6007959
-- title:
--   Ball Quot Len: exists param
-- statement:
--   The Ball Quot Len construction uses the exists param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L49-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L49-L113

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

theorem PI.UnitaryGroupMassFormula.BallQuotLen.exists_param [Finite (Pts O A)] (ζ₀ : Pts O A) [IsDVRAt ζ₀] :
    ∃ t : ↥(As O A), vL ζ₀ t = 1 ∧ ∀ ζ : Pts O A, ζ ≠ ζ₀ → t ∉ ζ.asIdeal := by sorry
