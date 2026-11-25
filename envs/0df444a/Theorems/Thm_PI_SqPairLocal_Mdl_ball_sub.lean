-- Prove2me | Theorems.Thm_PI_SqPairLocal_Mdl_ball_sub
-- name    : PI.SqPairLocal.Mdl.ball_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:31.321104+00:00
-- url     : https://prove2.me/theorems/c8f83758-fc19-4e57-b6d4-eff11de58128
-- title:
--   Mdl: ball sub
-- statement:
--   The Mdl construction uses the ball sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L13-L22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_PowerSeriesExpansionImageDenseWithDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain HeightOneSpectrum WithZero IsLocalRing Topology Filter
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
open PI PI.SqPairLocal PI.SqPairLocal.Mdl
open PI.SqPairLocal Formalism.BasicNotions.Examples₂
variable {E : Type} [Field E] [NumberField E] [StarRing E] (v : HeightOneSpectrum (𝓞 E))

theorem PI.SqPairLocal.Mdl.ball_sub (x : v.adicCompletion E) {s : Set (v.adicCompletion E)} (hs : s ∈ 𝓝 x) :
    ∃ K : ℕ, ∀ z : v.adicCompletion E, Valued.v (z - x) ≤ exp (-(K : ℤ)) → z ∈ s := by sorry
