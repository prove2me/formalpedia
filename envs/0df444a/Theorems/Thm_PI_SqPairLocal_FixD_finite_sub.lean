-- Prove2me | Theorems.Thm_PI_SqPairLocal_FixD_finite_sub
-- name    : PI.SqPairLocal.FixD.finite_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:28:27.728944+00:00
-- url     : https://prove2.me/theorems/8cb58e5e-5e90-56dc-8857-7ba38b0e2082
-- title:
--   Fix D: finite sub
-- statement:
--   The Fix D construction uses the finite sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L138-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L138-L140

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

theorem PI.SqPairLocal.FixD.finite_sub [IsLocalRing R] [IsLocalRing (fixSub σ)] [Finite (ResidueField R)] :
    Finite (ResidueField (fixSub σ)) := by sorry
