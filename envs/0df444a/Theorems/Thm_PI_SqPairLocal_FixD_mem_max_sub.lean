-- Prove2me | Theorems.Thm_PI_SqPairLocal_FixD_mem_max_sub
-- name    : PI.SqPairLocal.FixD.mem_max_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:28:14.78154+00:00
-- url     : https://prove2.me/theorems/48cb7e3b-205e-598b-a384-e794d021db26
-- title:
--   Fix D: mem max sub
-- statement:
--   The Fix D construction uses the mem max sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L61-L63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI PI.SqPairLocal PI.SqPairLocal.FixD
variable {R : Type} [CommRing R] [IsDomain R] (σ : R ≃+* R)

theorem PI.SqPairLocal.FixD.mem_max_sub [IsLocalRing R] [IsLocalRing (fixSub σ)] (x : fixSub σ) :
    x ∈ maximalIdeal (fixSub σ) ↔ (x : R) ∈ maximalIdeal R := by sorry
