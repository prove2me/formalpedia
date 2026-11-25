-- Prove2me | Theorems.Thm_PI_LocDualGen_EpS_trace_eq
-- name    : PI.LocDualGen.EpS.trace_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:03.966431+00:00
-- url     : https://prove2.me/theorems/7b7a8f51-f91b-521a-87d2-6e98bc95d66c
-- title:
--   Ep S: trace eq
-- statement:
--   The Ep S construction uses the trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L99-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualSplit.lean#L99-L108

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

theorem PI.LocDualGen.EpS.trace_eq (z : L) : Algebra.trace K L z = pr hr e he h0 h1 0 z + pr hr e he h0 h1 1 z := by sorry
