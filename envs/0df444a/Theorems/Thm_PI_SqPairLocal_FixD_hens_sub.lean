-- Prove2me | Theorems.Thm_PI_SqPairLocal_FixD_hens_sub
-- name    : PI.SqPairLocal.FixD.hens_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:28:00.43537+00:00
-- url     : https://prove2.me/theorems/30c0405b-6b06-508e-85b7-f8e6faf1bbf3
-- title:
--   Fix D: hens sub
-- statement:
--   The Fix D construction uses the hens sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L92-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L92-L133

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

theorem PI.SqPairLocal.FixD.hens_sub [HenselianLocalRing R] [IsLocalRing (fixSub σ)] : HenselianLocalRing (fixSub σ) := by sorry
