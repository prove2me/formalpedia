-- Prove2me | Theorems.Thm_PI_LocDualGen_EpS_mem_of_isIntegral
-- name    : PI.LocDualGen.EpS.mem_of_isIntegral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:11.033885+00:00
-- url     : https://prove2.me/theorems/aad7890b-911e-46ae-a74a-249165cf198b
-- title:
--   Ep S: mem of is Integral
-- statement:
--   The Ep S construction uses the mem of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L35-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module
open PI PI.LocDualGen PI.LocDualGen.EpS
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]
variable [ValuativeRel K]

theorem PI.LocDualGen.EpS.mem_of_isIntegral {c : K} (h : IsIntegral 𝒪[K] c) : c ∈ 𝒪[K] := by sorry
