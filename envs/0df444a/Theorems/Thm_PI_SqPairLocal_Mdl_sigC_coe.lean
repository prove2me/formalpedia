-- Prove2me | Theorems.Thm_PI_SqPairLocal_Mdl_sigC_coe
-- name    : PI.SqPairLocal.Mdl.sigC_coe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:45:12.08772+00:00
-- url     : https://prove2.me/theorems/2132a4ff-957c-4629-8b6a-eb10dbfdd609
-- title:
--   Mdl: sig C coe
-- statement:
--   The Mdl construction uses the sig C coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SigKApply.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SigKApply.lean#L90-L92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply
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
open PI PI.SqPairLocal PI.SqPairLocal.Mdl
open PI.SqPairLocal Formalism.BasicNotions.Examples₂
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable (v : HeightOneSpectrum (𝓞 E)) (hv : v.asIdeal.comap (cj E) = v.asIdeal)
include hv

theorem PI.SqPairLocal.Mdl.sigC_coe (x : WithVal (v.valuation E)) :
    sigC v hv (x : (v.valuation E).Completion) = (tau v x : (v.valuation E).Completion) := by sorry
