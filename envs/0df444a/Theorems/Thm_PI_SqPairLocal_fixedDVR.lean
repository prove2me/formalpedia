-- Prove2me | Theorems.Thm_PI_SqPairLocal_fixedDVR
-- name    : PI.SqPairLocal.fixedDVR
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:25:30.109345+00:00
-- url     : https://prove2.me/theorems/cb00cc70-b3f8-42db-be89-3bde45a5f024
-- title:
--   Sq Pair Local: fixed DVR
-- statement:
--   The Sq Pair Local construction uses the fixed DVR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L145-L149

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
open PI.SqPairLocal
open FixD

theorem PI.SqPairLocal.fixedDVR : FixedDVR := by sorry
