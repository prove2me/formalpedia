-- Prove2me | Theorems.Thm_PI_LocDualGen_EpS_selfDual_split
-- name    : PI.LocDualGen.EpS.selfDual_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:00.989146+00:00
-- url     : https://prove2.me/theorems/893f391c-5c56-52a6-85ff-c369a7aa8706
-- title:
--   Ep S: self Dual split
-- statement:
--   The Ep S construction uses the self Dual split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L130-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L130-L145

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
include hr he h0 h1

theorem PI.LocDualGen.EpS.selfDual_split (x : L) :
    (∀ y : L, IsIntegral 𝒪[K] y → Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ IsIntegral 𝒪[K] x := by sorry
