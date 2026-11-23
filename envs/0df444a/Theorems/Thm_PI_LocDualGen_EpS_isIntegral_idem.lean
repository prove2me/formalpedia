-- Prove2me | Theorems.Thm_PI_LocDualGen_EpS_isIntegral_idem
-- name    : PI.LocDualGen.EpS.isIntegral_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:27.606833+00:00
-- url     : https://prove2.me/theorems/88775890-1699-442b-bccf-312090fb2129
-- title:
--   Ep S: is Integral idem
-- statement:
--   The Ep S construction uses the is Integral idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L30-L33

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

theorem PI.LocDualGen.EpS.isIntegral_idem (e : L) (he : IsIdempotentElem e) : IsIntegral 𝒪[K] e := by sorry
