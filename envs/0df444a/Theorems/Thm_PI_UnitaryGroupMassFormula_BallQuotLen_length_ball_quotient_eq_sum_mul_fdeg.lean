-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_length_ball_quotient_eq_sum_mul_fdeg
-- name    : PI.UnitaryGroupMassFormula.BallQuotLen.length_ball_quotient_eq_sum_mul_fdeg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:57.825545+00:00
-- url     : https://prove2.me/theorems/f7eb95c1-0505-43de-8df6-a891d25b905d
-- title:
--   Ball Quot Len: length ball quotient eq sum mul fdeg
-- statement:
--   The Ball Quot Len construction uses the length ball quotient eq sum mul fdeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L347-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L347-L399

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
variable {V : Type*} [AddCommGroup V] [Module A V] [Module O V] [IsScalarTower O A V] {e : V}

theorem PI.UnitaryGroupMassFormula.BallQuotLen.length_ball_quotient_eq_sum_mul_fdeg (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Fintype (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ)
    (hfin : Module.Finite O ↥(As O A)) (he : IsGen A e) :
    ∀ (n : ℕ) (c : Pts O A → ℤ) (m : Pts O A → ℕ), ∑ ζ, m ζ = n →
      Module.length O (↥(ballO ϖ e (fun ζ => c ζ + m ζ)) ⧸
          (ballO ϖ e c).comap (ballO ϖ e (fun ζ => c ζ + m ζ)).subtype) =
        ((∑ ζ, m ζ * fdeg ζ : ℕ) : ℕ∞) := by sorry
