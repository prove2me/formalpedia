-- Prove2me | Theorems.Thm_PI_SqPairLocal_FixD_isUnit_iff_sub
-- name    : PI.SqPairLocal.FixD.isUnit_iff_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:18.260402+00:00
-- url     : https://prove2.me/theorems/9406d562-85d1-4940-85d9-bec7c5fa3f20
-- title:
--   Fix D: is Unit iff sub
-- statement:
--   The Fix D construction uses the is Unit iff sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L24-L25

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

theorem PI.SqPairLocal.FixD.isUnit_iff_sub (x : fixSub σ) : IsUnit x ↔ IsUnit (x : R) := by sorry
