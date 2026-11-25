-- Prove2me | Theorems.Thm_PI_SqPairLocal_Mdl_sigK_apply
-- name    : PI.SqPairLocal.Mdl.sigK_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:30.266278+00:00
-- url     : https://prove2.me/theorems/73ea62fc-c63d-4fc7-9bfb-b477f5fc1463
-- title:
--   Mdl: sig K apply
-- statement:
--   The Mdl construction uses the sig K apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SigKApply.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SigKApply.lean#L106-L107

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

theorem PI.SqPairLocal.Mdl.sigK_apply (x : v.adicCompletion E) :
    sigK v hv x = adicCompletion.ofCompletion (sigC v hv x.toCompletion) := by sorry
