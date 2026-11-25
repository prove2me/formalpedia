-- Prove2me | Theorems.Thm_PI_SqPairLocal_Mdl_alg_int_mem
-- name    : PI.SqPairLocal.Mdl.alg_int_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:50.791811+00:00
-- url     : https://prove2.me/theorems/4b401fbe-58b0-4845-bc70-27e9a17d2616
-- title:
--   Mdl: alg int mem
-- statement:
--   The Mdl construction uses the alg int mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L83-L85

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
variable (hv : v.asIdeal.comap (cj E) = v.asIdeal)
include hv

theorem PI.SqPairLocal.Mdl.alg_int_mem (y : 𝓞 E) :
    algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y) ∈ v.adicCompletionIntegers E := by sorry
