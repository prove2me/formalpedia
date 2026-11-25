-- Prove2me | Theorems.Thm_PI_VolStabS_FiniteFieldCounting_exp_id
-- name    : PI.VolStabS.FiniteFieldCounting.exp_id
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:02.806424+00:00
-- url     : https://prove2.me/theorems/19928c42-7fdd-5572-9990-06ffb829266b
-- title:
--   Finite Field Counting: exp id
-- statement:
--   The Finite Field Counting construction uses the exp id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFT.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFT.lean#L52-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldCounting

theorem PI.VolStabS.FiniteFieldCounting.exp_id (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by sorry
