-- Prove2me | Theorems.Thm_PI_SqPairLocal_Mdl_sigK_int
-- name    : PI.SqPairLocal.Mdl.sigK_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:25.812614+00:00
-- url     : https://prove2.me/theorems/9887b664-8c63-494d-b937-ce0614379597
-- title:
--   Mdl: sig K int
-- statement:
--   The Mdl construction uses the sig K int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/PowerSeriesExpansionImageDenseWithDenominator.lean#L78-L81

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

theorem PI.SqPairLocal.Mdl.sigK_int (y : 𝓞 E) :
    sigK v hv (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y)) =
      algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E (cj E y)) := by sorry
