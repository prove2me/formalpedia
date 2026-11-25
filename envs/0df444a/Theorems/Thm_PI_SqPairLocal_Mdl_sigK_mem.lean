-- Prove2me | Theorems.Thm_PI_SqPairLocal_Mdl_sigK_mem
-- name    : PI.SqPairLocal.Mdl.sigK_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:42.164618+00:00
-- url     : https://prove2.me/theorems/9a9bfdda-8e7b-594e-a146-04f0cd3e86aa
-- title:
--   Mdl: sig K mem
-- statement:
--   The Mdl construction uses the sig K mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L87-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L87-L104

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

theorem PI.SqPairLocal.Mdl.sigK_mem (x : v.adicCompletion E) (hx : x ∈ v.adicCompletionIntegers E) :
    sigK v hv x ∈ v.adicCompletionIntegers E := by sorry
