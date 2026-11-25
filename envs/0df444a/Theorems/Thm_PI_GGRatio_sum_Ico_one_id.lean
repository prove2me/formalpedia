-- Prove2me | Theorems.Thm_PI_GGRatio_sum_Ico_one_id
-- name    : PI.GGRatio.sum_Ico_one_id
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:31:12.246411+00:00
-- url     : https://prove2.me/theorems/0e57787f-2168-4932-b224-1c62010f5572
-- title:
--   GGRatio: sum Ico one id
-- statement:
--   The GGRatio construction uses the sum Ico one id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GenericRatioBound/GenericRatioOfBound.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GenericRatioBound/GenericRatioOfBound.lean#L8-L12

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GenericRatioBound_GenericRatioOfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGRatio
open Finset

theorem PI.GGRatio.sum_Ico_one_id (k : ℕ) : ∑ i ∈ Ico 1 k, i = k * (k - 1) / 2 := by sorry
