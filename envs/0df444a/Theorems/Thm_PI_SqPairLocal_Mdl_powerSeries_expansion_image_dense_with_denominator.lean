-- Prove2me | Theorems.Thm_PI_SqPairLocal_Mdl_powerSeries_expansion_image_dense_with_denominator
-- name    : PI.SqPairLocal.Mdl.powerSeries_expansion_image_dense_with_denominator
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:23.59987+00:00
-- url     : https://prove2.me/theorems/aa07a899-4b97-496a-b446-2c5faef75d79
-- title:
--   Mdl: power Series expansion image dense with denominator
-- statement:
--   The Mdl construction uses the power Series expansion image dense with denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L47-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L47-L71

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

theorem PI.SqPairLocal.Mdl.powerSeries_expansion_image_dense_with_denominator (x : v.adicCompletion E) (hx : x ∈ v.adicCompletionIntegers E) (K : ℕ) :
    ∃ y : 𝓞 E, Valued.v (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y) - x) <
      exp (-(K : ℤ)) := by sorry
