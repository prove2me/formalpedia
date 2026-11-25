-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_length_step
-- name    : PI.UnitaryGroupMassFormula.BallQuotLen.length_step
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:01.537742+00:00
-- url     : https://prove2.me/theorems/7a60c19a-4429-4042-9ec8-ea4e1b72b237
-- title:
--   Ball Quot Len: length step
-- statement:
--   The Ball Quot Len construction uses the length step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L266-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BallQuotientLength/LengthBallQuotientEqSumMulFdeg.lean#L266-L345

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
open Classical

theorem PI.UnitaryGroupMassFormula.BallQuotLen.length_step (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Finite (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (hfin : Module.Finite O ↥(As O A))
    (he : IsGen A e) (c d : Pts O A → ℤ) (ζ₀ : Pts O A)
    (hd : ∀ ζ, d ζ = c ζ + if ζ = ζ₀ then 1 else 0) :
    Module.length O (↥(ballO ϖ e d) ⧸ (ballO ϖ e c).comap (ballO ϖ e d).subtype) = fdeg ζ₀ := by sorry
