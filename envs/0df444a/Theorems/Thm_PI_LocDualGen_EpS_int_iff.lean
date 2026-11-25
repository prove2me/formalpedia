-- Prove2me | Theorems.Thm_PI_LocDualGen_EpS_int_iff
-- name    : PI.LocDualGen.EpS.int_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:19.0078+00:00
-- url     : https://prove2.me/theorems/3ae98d63-d593-4ab5-8a24-18947825be59
-- title:
--   Ep S: int iff
-- statement:
--   The Ep S construction uses the int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L112-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L112-L126

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
variable (hr : finrank K L = 2) (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1)
variable [ValuativeRel K]

theorem PI.LocDualGen.EpS.int_iff (z : L) :
    IsIntegral 𝒪[K] z ↔ pr hr e he h0 h1 0 z ∈ 𝒪[K] ∧ pr hr e he h0 h1 1 z ∈ 𝒪[K] := by sorry
